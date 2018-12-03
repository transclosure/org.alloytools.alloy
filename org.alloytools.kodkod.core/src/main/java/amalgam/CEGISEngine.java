package amalgam;

import kodkod.ast.*;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.*;

import java.util.*;
import java.util.function.Predicate;
import java.util.logging.*;

import static amalgam.Logger.*;
import static amalgam.CEGISHelpers.*;

/**
 * Prototype of 4-part CEGIS synthesis loop for finding initial deployable configurations.
 * Exclusion refers to excluding some slice of the potential deployable-initial-config space, NOT trace exclusion.
 */
public class CEGISEngine {
    // CEGIS parameters (options in CEGISHelpers)
    private SynthProblem problem;
    private CEGISBase base;
    // CEGIS runtime
    private final Map<CEGISPHASE, Long> transtotal = new HashMap<>();
    private final Map<CEGISPHASE, Long> solvetotal = new HashMap<>();
    private long coreMinTotal = 0;
    private IncrementalSolver synthSolver = null;

    /**
     * TODO
     * @param problem
     * @throws CEGISException
     */
    public CEGISEngine(SynthProblem problem) throws CEGISException {
        this.problem = problem;
        this.base = new CEGISBase(problem);
        Logger.init();
        validate();
    }

    /**
     * TODO
     * @throws CEGISException
     */
    public void run() throws CEGISException {
        long startTime = System.currentTimeMillis();
        output("\n\n===================================================================\nRunning problem: "+problem.desc());
        output(cegis());
        output("Total time (ms): "+(System.currentTimeMillis()-startTime)+
                ".\nTranslation: "+transtotal+
                ",\nsolve: "+solvetotal+
                ",\ncore minimization (note vulnerable to GC etc.): "+coreMinTotal);
    }

    /**
     * TODO
     * @throws CEGISException
     */
    private void validate() throws CEGISException {
        // Check that the problem given is well-formed. For instance, event relations must all contain "EVENT_" in their name.

        for(Relation r : problem.eventRelations()) {
            if(r.arity() < 2) throw new CEGISException("Validation failure: event relation "+r+" had arity < 2");
            if(!r.toString().contains("EVENT_"))
                throw new CEGISException("Validation failure: "+r+" was an event relation but did not contain EVENT_ in name");
        }
        for(Relation r : problem.deployableRelations()) {
            if(r.arity() < 2) throw new CEGISException("Validation failure: state relation "+r+" had arity < 2");
            if(r.toString().contains("EVENT_"))
                throw new CEGISException("Validation failure: "+r+" was *NOT* an event relation but contained EVENT_ in name");
        }
        for(Relation r : problem.nondeployableRelations()) {
            if(r.arity() < 2) throw new CEGISException("Validation failure: state relation "+r+" had arity < 2");
            if(r.toString().contains("EVENT_"))
                throw new CEGISException("Validation failure: "+r+" was *NOT* an event relation but contained EVENT_ in name");
        }
        // TODO likely more checks to do here, but the interface/API are still very fluid, so not spending much time on it yet
    }

    /**
     * TODO
     * @return
     */
    private String cegis() throws CEGISException {
        int loopCount = 0;
        Bounds synthbounds = base.buildBounds(1);
        // Start with the basic constraints (may be some a priori limitations on what is a well-formed constraint)
        // as well as structural constraints (don't produce a malformed cfg)
        Formula synthformula = Formula.and(problem.additionalInitialConstraintsP1P2(first))
                          .and(Formula.and(problem.structuralAxioms(state)));

        while(loopCount++<loopLimit) {
            output(Level.INFO, "------------------------- Loop:"+loopCount+"-------------------------");

            ////////////////////////////////////////////////
            // Step 1: synthesize
            Solution sol = execIncrementalSynth(synthformula, synthbounds);
            stats(sol, CEGISPHASE.SYNTH);
            if(sol.sat()) {
                output(Level.INFO, "Candidate: "+problem.prettyConfigFromSynth(sol)+"\n");
            }
            else {
                output(Level.INFO, "synth failed, unsat: "+sol.outcome());
                return "Synthesis step failed with UNSAT";
            }

            ////////////////////////////////////////////////
            // Step 2: verify
            Bounds cebounds = base.buildBounds(numStates);
            Solution ce =  execNonincrementalCE(base.ceFormula(cebounds,false, false, sol), cebounds);
            stats(ce, CEGISPHASE.COUNTER);
            if(ce.unsat()) return "Success in "+loopCount+" iterations!";
            else {
                output(Level.INFO, "Counterexample:\n"+ce.instance().relationTuples()+"\n");
            }

            ////////////////////////////////////////////////
            // Step 3: localize trace literals responsible for the property violation (proximate cause)
            // i.e., ask first why the trace violates the property, irrespective of the system transition rules

            // Note on implementation: we can't just add the concrete trace as an exact bound. Then it wouldn't
            //  be used in the core at all, because those variables will be eliminated! instead, encode the trace as a fmla.

            // Include phi, but not system axioms.
            Formula whyCEFormula = base.ceFormula(cebounds,true, true, sol);
            // Also include the entire trace from start to finish
            Formula whyTFormula = base.fixTraceAsFormula(ce, cebounds, new HashSet<>(), numStates);
            output(Level.FINER, "S3: whyCEFormula="+whyCEFormula);
            output(Level.FINER, "S3: whyTFormula="+whyTFormula);
            Solution why = execNonincrementalCE(whyCEFormula.and(whyTFormula), cebounds);
            stats(why, CEGISPHASE.PROXIMAL);
            if(why.sat()) {
                output(Level.INFO, "\n"+why.instance());
                return "Error: counterexample-why step returned SAT for property on CE trace.";
            }
            // HybridStrategy is giving non-minimal cores, so use RCE
            long beforeCore1 = System.currentTimeMillis();
            why.proof().minimize(new RCEStrategy(why.proof().log()));
            Set<Formula> reasons = new HashSet(why.proof().highLevelCore().keySet());
            coreMinTotal += (System.currentTimeMillis() - beforeCore1);
            // Trying new Java8 filter. sadly .equals on the fmla isnt enough, so pretend and use .toString()
            Predicate isAPhi = f -> f.toString().equals(Formula.and(problem.goals(state, enext)).toString()); // TODO: enext needs to be "enhanced enext", with lasso
            reasons.removeIf(isAPhi);
            output(Level.INFO, "PROXIMAL CAUSE: "+reasons);


            ////////////////////////////////////////////////
            // Step 4: find root cause (in initial deployable config) of proximate cause
            // We have a set of "reason" formulas. These may involve multiple states.
            // Ask: why is their conjunction necessary? This loop is set up to seek immediate causes in the prestate,
            // because it's easy to get an unhelpful core that might (e.g.) blame the state *AFTER* the one with the reason.
            // It's also possible to get cores that point to things in the same state. Because of this, we create a problem
            // that fixes the prestate literals but only the (negated) reason literals in the poststate.

            // TODO: separate solver, single step per invocation? want push/pop!

            Set<Formula> initialReasons = new HashSet<>();

            // until all blame obligations are discharged, keep moving toward initial state
            int lastMTL = Integer.MAX_VALUE;
            while(!reasons.isEmpty()) {
                output(Level.INFO, "Deriving blame for: "+reasons+"; mtl: "+maxTraceLength(reasons));

                // We have a set of reasons to derive root-cause for.
                // Because this set of reasons may involve multiple states, we should be starting with the latest
                // reasons, re-sorting every iteration. (It should be OK to combine reasons from the same state.)
                // If we don't do this, we'll get unsound results from looking at individual pre/post state windows.
                int mtl = maxTraceLength(reasons);
                Set<Formula> delayedReasons = new HashSet<>();
                for(Formula f: reasons) {
                    int fmtl = maxTraceLength(f);
                    if(fmtl < mtl) delayedReasons.add(f);
                }
                reasons.removeAll(delayedReasons); // Obligation to re-add this set at end
                if(!delayedReasons.isEmpty()) output(Level.INFO, "Delaying finding root causes for: "+delayedReasons);

                // Prevent looping forever in case the blame process is not making progress; should always reduce mtl
                if(mtl >= lastMTL) {
                    throw new RuntimeException("Potentially malformed or anti-causal transition relation. Reasons: "+reasons);
                } else {
                    lastMTL = mtl;
                }

                // Because we're limiting ourselves to 2 states, need to rewrite state expressions in reasons.
                Set<Formula> rewrittenReasons = new HashSet<>();
                for(Formula f : reasons) {
                    rewrittenReasons.add(rewriteStateLiteralDepth(f, 2)); // second state
                }
                output(Level.FINER, "Rewritten reasons: "+rewrittenReasons);

                // Negate the trace literals we want explained
                Bounds blamebounds = base.buildBounds(2); // include ONLY TWO STATES
                Formula blameCEFormula = base.ceFormula(blamebounds,true, false, sol);
                // Include this prestate (reason -1 depth) and negated reasons
                Set<Formula> blameTransitionFormula = base.fixPreTransitionAsFormula(ce, blamebounds, buildStateExpr(mtl-1), first,false, rewrittenReasons);

                //System.out.println("BTF: "+blameTransitionFormula);
                Solution blame = execNonincrementalCE(blameCEFormula.and(Formula.and(blameTransitionFormula)), blamebounds);
                stats(blame, CEGISPHASE.ROOT);
                if(blame.sat()) {
                    output(Level.INFO, "\n"+blame.instance().relationTuples());
                    return "Error: Root-cause extraction step returned SAT for transition; expected unsat.";
                }

                // HybridStrategy is producing vastly non-minimal cores on Theo+hack. Use RCE to get guaranteed minimum.
                //blame.proof().minimize(new HybridStrategy(blame.proof().log()));
                long beforeCore2 = System.currentTimeMillis();
                blame.proof().minimize(new RCEStrategy(blame.proof().log()));
                // Slower than RCEStrategy for this problem
                //blame.proof().minimize(new DynamicRCEStrategy(blame.proof().log()));
                HashSet<Formula> localCause = new HashSet<>(blame.proof().highLevelCore().keySet());
                coreMinTotal += (System.currentTimeMillis() - beforeCore2);

                output(Level.FINER, "BLAME core (all MTL fmlas, NOT rewritten): "+localCause);
                System.out.println("BLAME core (all MTL fmlas, NOT rewritten): "+localCause);
                // Strip out local causes that aren't trace literals
                HashSet<Formula> toRemove = new HashSet<>();
                for(Formula f: localCause) {
                    // Not a trace literal (likely one of the transition axioms)
                    if(!isTraceLiteral(f)) {
                        toRemove.add(f);
                    }
                    // The negated goal that we added before
                    if(isOneOfNegated(f, rewrittenReasons)) {
                        toRemove.add(f);
                    }
                }
                localCause.removeAll(toRemove);

                output(Level.INFO, "BLAME core (post filter): "+localCause);

                // If filtered core is empty, we've found a contradiction in the spec.
                if(localCause.isEmpty()) {
                    String prettyCore = "";
                    for(Formula f : toRemove) {
                        prettyCore += f + "\n";
                    }

                    output(Level.INFO,
                            "==========================================================================\n"+
                            "Contradiction found in backtracing to root cause. It is possible that you are seeing this\n" +
                            "because the problematic behavior cannot be prevented by any initial deployable config.\n"+
                            "Pre-filter core was *independent* of prestate. It was: \n"+prettyCore+"\n"+
                            "Remember that these are rewritten formulas; mtl was: "+mtl);
                    return "==========================================================================\n"+
                            "Synthesis failed due to contradiction in backtracing to root cause. "+
                            "It is possible that the synthesizer identified problematic behavior that "+
                            "cannot be prevented by any initial deployable config. See logs for more information.";
                }


                Set<Formula> localCauseRewritten = new HashSet<>();
                for(Formula f : localCause) {
                    if(maxTraceLength(f) != 1) throw new RuntimeException("blame stage returned non-causal core fmla: "+f);
                    localCauseRewritten.add(rewriteStateLiteralDepth(f, mtl-1));
                }

                output(Level.INFO, "Blame core filtered and rewritten: "+localCauseRewritten);

                // Finalize local causes that are about the initial state; add others to reasons and iterate
                reasons.clear();
                // Make sure there's no non-trace literals in delayedreasons (e.g., event literals)
                // sadly .equals on the fmla isnt enough, so pretend and use .toString()
                Predicate<Formula> isntTraceLiteral = f -> !isTraceLiteral(f);
                delayedReasons.removeIf(isntTraceLiteral);
                reasons.addAll(delayedReasons); // re-add reasons that happened earlier in the trace than current transition
                for(Formula f: localCauseRewritten) {
                    // I can't believe I'm doing this...
                    boolean needsMore = f.toString().contains(STR_FIRSTNEXT);
                    if(!needsMore) initialReasons.add(f);
                    else reasons.add(removeDoubleNegation(f));
                }
            } // continue moving toward true root cause

            output(Level.INFO, "Final blame set in initial state:"+initialReasons);
            Formula initialStateCause = Formula.and(initialReasons);

            // FINALLY: extend synth formula
            // using IncrementalSolver now, so formula is the *delta*
            synthformula = initialStateCause.not();

            synthbounds = new Bounds(base.universe); // empty bounds for followup calls to IncrementalSolver
            // To measure performance vs. non-incremental, just restore original fmla/bnds and call normal exec
        }
        return "TIMEOUT: loop limit of "+loopLimit+" exceeded.";
    }

    /**
     * TODO
     * @param sol
     * @param phase
     */
    private void stats(Solution sol, CEGISPHASE phase) {
        // Core minimization time is recorded elsewhere
        String sat = sol.sat() ? "sat" : "unsat";
        long trans = sol.stats().translationTime();
        long solve = sol.stats().solvingTime();
        output(Level.FINE, phase+" trans ms: " + trans + "\tsolve ms: "+ solve + "\t sat: " + sat);
        updateTimeMap(transtotal, phase, trans);
        updateTimeMap(solvetotal, phase, solve);
    }

    /**
     * TODO
     * @param m
     * @param p
     * @param add
     */
    private void updateTimeMap(Map<CEGISPHASE, Long> m, CEGISPHASE p, long add) {
        if(!m.keySet().contains(CEGISPHASE.SYNTH)) m.put(CEGISPHASE.SYNTH, Long.valueOf(0));
        if(!m.keySet().contains(CEGISPHASE.COUNTER)) m.put(CEGISPHASE.COUNTER, Long.valueOf(0));
        if(!m.keySet().contains(CEGISPHASE.PROXIMAL)) m.put(CEGISPHASE.PROXIMAL, Long.valueOf(0));
        if(!m.keySet().contains(CEGISPHASE.ROOT)) m.put(CEGISPHASE.ROOT, Long.valueOf(0));

        m.put(p, m.get(p)+add);
    }

    /**
     * TODO
     * @param f
     * @param b
     * @return
     */
    private Solution execIncrementalSynth(Formula f, Bounds b) {
        if(synthSolver == null) {
            Options options = new Options();
            options.setSolver(incrementalSolver);
            options.setSymmetryBreaking(20);
            options.setSkolemDepth(-1);
            options.setLogTranslation(0); // changed by TN from 2->0; MUST be 0 to use IncrementalSolver
            options.setBitwidth(bitwidth);
            options.setNoOverflow(true); // added TN
            synthSolver = IncrementalSolver.solver(options);
        }
        // Note: many important invariants for using this feature. See IncrementalSolver docs:
        /*
        If the first problem (f0, b0, opt) passed to the solver via the solve method is satisfiable,
        the resulting solution and the underlying incremental SAT solver are saved. When the solve method
         is called again with a new formula f1 and bounds b1, the translation of (f1, b1, opt) is added to
         the stored SAT solver, which is then called to obtain a solution for the problem f0 && f1 and b0 + b1.
          We define b0 + b1 to be a disjoint union of the bindings in b0 and b1, where b0.universe = b1.universe,
           b1.intBound is empty, and b1 contains no bindings for relations that are bound by b0.
           This process can be repeated until the solver yields UNSAT.
         */
        // NB: ***and b1 contains no bindings for relations that are bound by b0***
        // So pass an empty bounds?
        return synthSolver.solve(f, b);
    }

    /**
     * TODO
     * @param f
     * @param b
     * @return
     */
    private Solution execNonincrementalCE(Formula f, Bounds b) {
        // TODO (OPT): ideally we could clone copies of a base solver state to avoid re-translation
        //  (indeed, SMT provides this very thing with pop/push)
        // TODO (OPT): trace minimization (iterative deepening? aluminum won't work due to snags)
        final Solver solver = new Solver();
        solver.options().setSolver(coreSolver);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(-1);
        solver.options().setLogTranslation(2);
        solver.options().setCoreGranularity(3); // max = 3
        solver.options().setBitwidth(bitwidth);
        solver.options().setNoOverflow(true); // added TN
        return solver.solve(f, b);
    }
}

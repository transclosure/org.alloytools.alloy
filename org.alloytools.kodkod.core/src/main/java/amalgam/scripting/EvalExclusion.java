package amalgam.scripting;

/*
  Theo's spec, with changes to comfyAt relation.

 */

import amalgam.examples.HomeNet;
import amalgam.examples.KodkodExample;
import kodkod.ast.*;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;
import kodkod.engine.SolutionIterator;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.*;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

// TODO trace min (iterative deepening? aluminum won't work due to snags)
// TODO   could also just edit the instance + evaluate, for now. likely to be faster but less flexible

public class EvalExclusion {

    final static int loopLimit = 1000;
    final static int numStates = 10;
    final static int minInt = -128;
    final static int maxInt = 127;

    public static void main(String[] args) {
        long curr = System.currentTimeMillis();
        setupBaseUniverse();
        System.out.println(cegis());
        System.out.println("Total time (ms): "+(System.currentTimeMillis()-curr)+" translation: "+transtotal+" solving:"+solvetotal);
    }

    private static Relation next = Relation.binary("next");
    private static Relation state = Relation.unary("State");
    private static Relation first = Relation.unary("first");
    private static Relation last = Relation.unary("last");
    private static Relation setting = Relation.binary("setting");
    private static Relation next_p = Relation.binary("next_p");
    private static Relation next_target = Relation.binary("next_target");

    private static Relation comfyAt = Relation.binary("comfyAt");
    private static Relation canSet = Relation.unary("CONF_canSet");
    private static Relation allowedTemp = Relation.unary("CONF_allowedTemp");
    private static Relation personA = Relation.unary("PersonA");
    private static Relation personB = Relation.unary("PersonB");
    private static Universe universe;
    private static TupleFactory factory;

    private static Formula baseSynthFormula() {
        Formula tension1 = (canSet.join(comfyAt)).intersection(allowedTemp).some();
        Variable p = Variable.unary("p");
        // Using forall, anticipating more people eventually
        Formula tension2 = p.join(comfyAt).intersection(allowedTemp).count().gt(IntConstant.constant(1)).forAll(p.oneOf(personA.union(personB)));
        return tension1.and(tension2);
    }

    private static Formula ceFormula() {
        // Concrete starting config = set as bounds

        // TODO: is it safe to omit this? bounds below force a single specific total ordering on <n> states
        //Formula te = next.totalOrder(state, first, last);

        Variable p = Variable.unary("p");
        Variable s = Variable.unary("s");

        // setting, next_p, next_target relations are functional
        Formula structure = setting.function(state, Expression.INTS)
                .and(next_p.function(state, personA.union(personB))) // TODO: person relation
                .and(next_target.function(state, Expression.INTS));

        // Start in a state where everyone is comfy
        //  all p: Person | s.setting in p.comfyAt    [applied to first]
        Formula initial = first.join(setting).in(p.join(comfyAt)).forAll(p.oneOf(personA.union(personB)));

        // This is a concrete trace of the system
        Formula transition = buildTransition(s, s.join(next));
        Formula trace = transition.forAll(s.oneOf(state.difference(last)));

        //  negated: all s: State | all p: Person | s.setting in p.comfyAt
        Formula property = s.join(setting).in(p.join(comfyAt)).forAll(p.oneOf(personA.union(personB))).forAll(s.oneOf(state));
        Formula notProperty = property.not();

        return structure.and(initial).and(trace).and(notProperty);
    }

    // The transition predicate on [s, s'] (minus type annotations, beware)
    private static Formula buildTransition(Expression s, Expression s2) {
        return buildTransitionPrim(s.join(setting), s.join(next_p), s.join(next_target), s2.join(setting));
    }

    private static Formula buildTransitionPrim(Expression pretemp, Expression p, Expression targ, Expression posttemp) {
        Formula ante = p.in(canSet).and(targ.in(allowedTemp));
        Formula thenf = posttemp.eq(targ);
        Formula elsef = posttemp.eq(pretemp);
        Formula transition = ante.implies(thenf).and(ante.not().implies(elsef));
        return transition;
    }

    private static Formula breakTransition(Solution ce, Object preatom, Object postatom) {
        // Extract pretemp, next_p, next_target, posttemp
        IntConstant pretemp = null;
        Relation p = null;
        IntConstant targ = null;
        IntConstant posttemp = null;

        // Casting/comparisons to null necessary because raw atoms are just Object :-(

        for(Tuple s : ce.instance().relationTuples().get(setting)) {
            Object sstate = s.atom(0);
            if(sstate.equals(preatom)) {
                pretemp = IntConstant.constant((Integer)s.atom(1));
            }
            if(sstate.equals(postatom)) {
                posttemp = IntConstant.constant((Integer)s.atom(1));
            }
        }
        for(Tuple s : ce.instance().relationTuples().get(next_p)) {
            Object sstate = s.atom(0);
            if (sstate.equals(preatom)) {
                Object pa = s.atom(1);
                // TODO: build a table to get back to person expressions
                if(pa.equals("PersonA")) p = personA;
                else if(pa.equals("PersonB")) p = personB;
                else throw new IllegalArgumentException("no person expression built for "+pa.toString());
            }
        }
        for(Tuple s : ce.instance().relationTuples().get(next_target)) {
            Object sstate = s.atom(0);
            if (sstate.equals(preatom)) {
                targ = IntConstant.constant((Integer)s.atom(1));
            }
        }

        if(pretemp != null && p != null && targ != null && posttemp != null)
            return buildTransitionPrim(pretemp.toExpression(), p, targ.toExpression(), posttemp.toExpression()).not();
        else
            throw new IllegalArgumentException("unable to build: "+pretemp+";"+p+";"+targ+";"+posttemp);
    }


    private static Formula traceExclusion(Solution ce) {
        //ce.instance().relationTuples().get(first) // always State0

        List<Formula> subs = new ArrayList<>();

        // TODO: break initial

        for(Tuple nxt : ce.instance().relationTuples().get(next)) {
            Object pre = nxt.atom(0);
            Object post = nxt.atom(1);

            // Note this isn't just buildTransition(pre, post).not()
            //   because we don't have explicit state atoms to work with
            subs.add(breakTransition(ce, pre, post));
        }

        // Either first isn't first, or some transition is broken
        return Formula.or(subs);
    }


    private static Bounds ceBounds(TupleSet c_canSet, TupleSet c_allowedTemp) {
        // Start from synth bounds
        Bounds bounds = synthBounds();

        // Bound the configuration to be exactly what the last synth step produced
        bounds.boundExactly(canSet, c_canSet);
        bounds.boundExactly(allowedTemp, c_allowedTemp);

        // Create an explicit trace
        // TODO: exact bound = weakness. if make non-exact, be sure to add containment axioms
        List<Tuple> stateExactly = new ArrayList<>();
        List<Tuple> nextExactly = new ArrayList<>();
        List<Tuple> settingUpper = new ArrayList<>();
        List<Tuple> next_pUpper = new ArrayList<>();
        List<Tuple> next_targetUpper = new ArrayList<>();

        for(int i=0;i<numStates;i++) {
            stateExactly.add(factory.tuple("State"+i));
            if(i < numStates-1) {
                nextExactly.add(factory.tuple("State" + i, "State" + (i + 1)));
            }

            next_pUpper.add(factory.tuple("State"+i, "PersonA"));
            next_pUpper.add(factory.tuple("State"+i, "PersonB"));
            for(int j=minInt;j<=maxInt;j++) {
                next_targetUpper.add(factory.tuple("State"+i, j));
                settingUpper.add(factory.tuple("State"+i, j));
            }

        }
        bounds.boundExactly(state, factory.setOf(stateExactly));
        bounds.boundExactly(first, factory.setOf(factory.tuple("State0")));
        bounds.boundExactly(last, factory.setOf(factory.tuple("State"+(numStates-1))));
        bounds.boundExactly(next, factory.setOf(nextExactly));
        bounds.bound(setting, factory.setOf(settingUpper));
        bounds.bound(next_p, factory.setOf(next_pUpper));
        bounds.bound(next_target, factory.setOf(next_targetUpper));

        return bounds;
    }

    private static void setupBaseUniverse() {
        // Universe
        List<Object> atoms = new ArrayList<>();
        atoms.add("PersonA");
        atoms.add("PersonB");
        // Add atoms for each integer. TODO: is this the way in Kodkod 2?
        for(int i=minInt; i<=maxInt; i++) {
            atoms.add(Integer.valueOf(i));
        }
        for(int i=0;i<numStates;i++) {
            atoms.add("State" + i);
        }

        universe = new Universe(atoms);
        factory = universe.factory();
    }

    private static Bounds synthBounds() {
        // Relations
        List<Tuple> comfyAts = new ArrayList<>();
        List<Tuple> canSetUpper = new ArrayList<>();
        List<Tuple> allowedUpper = new ArrayList<>();

        // changed to narrower range on A, wider range on B, because was getting a good config on first synth...
        // Note we can't go to a single temp if we're requiring #overlap > 1 in fmla
        for(int i=70; i<=75; i++) {
            comfyAts.add(factory.tuple("PersonA", i));
        }
        for(int i=-100; i<=100; i++) {
            comfyAts.add(factory.tuple("PersonB", i));
        }
        canSetUpper.add(factory.tuple("PersonA"));
        canSetUpper.add(factory.tuple("PersonB"));

        for(int i=minInt; i<=maxInt; i++) {
            allowedUpper.add(factory.tuple(i));
        }
        // Bounds
        Bounds bounds = new Bounds(universe);
        bounds.boundExactly(comfyAt, factory.setOf(comfyAts));
        bounds.bound(canSet, factory.setOf(canSetUpper));
        bounds.bound(allowedTemp, factory.setOf(allowedUpper));
        bounds.boundExactly(personA, factory.setOf(factory.tuple("PersonA")));
        bounds.boundExactly(personB, factory.setOf(factory.tuple("PersonB")));

        // TODO: any issues with diff Tuple objects?
        // Set up integers as integers
        for(int i=minInt; i<=maxInt; i++) {
            bounds.boundExactly(i, factory.setOf(factory.tuple(i)));
        }

        return bounds;
    }

    private static Instance trimTrace(Instance ce, Formula f) {
        // Assume there's a trace in CE. Try to remove each step in succession.
        // TODO: reducing length to 2 actually doesn't help num of iterations much
        // so this might not be worth implementing
        return ce;
    }

    private static String cegis() {
        int loopCount = 0;
        Bounds synthbounds = synthBounds();
        Formula synthformula = baseSynthFormula();
        //SATFactory solver = SATFactory.Z3;
        SATFactory solver = SATFactory.MiniSat;

        final Formula ceformula = ceFormula(); // unchanging

        //Collection<Solution> counterexamples = new ArrayList<>();
        while(loopCount++<loopLimit) {
            // Step 1: synthesize
            Solution sol = execIncrementalSynth(synthformula, synthbounds, solver);
            stats(sol, "synth: ");
            if(sol.sat()) {
                //System.out.println(sol.instance());
                System.out.println(prettyConfig(sol));
            }
            else {
                System.out.println(synthbounds);
                System.out.println(synthformula);
                return "Synthesis step failed with UNSAT";
            }

            System.out.println();

            // Step 2: verify
            Bounds cebounds = ceBounds(
                    sol.instance().relationTuples().get(canSet),
                    sol.instance().relationTuples().get(allowedTemp));
            //System.out.println(cebounds);
            //System.out.println(cebounds.ints());
            //System.out.println(ceformula);
            Solution ce =  exec(ceformula, cebounds, solver);
            stats(ce, "verify: ");
            if(ce.unsat()) return "Success in "+loopCount+" iterations!";
            else {
                //System.out.println("CE:\n"+ce.instance());
            }
            // Step 2.25: trim CE trace
            Instance ceinst = ce.instance();
            ceinst = trimTrace(ceinst, ceformula);

            // Step 2.5: extend synth formula
            // using IncrementalSolver now, so formula is the *delta*
            //synthformula = synthformula.and(traceExclusion(ce));
            synthformula = traceExclusion(ce);
            System.out.println("te: "+synthformula);
            synthbounds = new Bounds(universe); // empty bounds for followup calls to IncrementalSolver
            // To measure performance vs. non-incremental, just restore original fmla/bnds and call normal exec
        }
        return "TIMEOUT: loop limit of "+loopLimit+" exceeded.";
    }

    private static String prettyConfig(Solution sol) {
        if(sol.sat()) {
            return "Allowed Temps: " + sol.instance().relationTuples().get(allowedTemp) + " " +
                    "Can Set: " + sol.instance().relationTuples().get(canSet);
        } else {
            return "UNSAT";
        }
    }

    private static int transtotal = 0;
    private static int solvetotal = 0;
    private static void stats(Solution sol, String prefix) {
        String sat = sol.sat() ? "sat" : "unsat";
        long trans = sol.stats().translationTime();
        long solve = sol.stats().solvingTime();
        System.out.println(prefix+"trans ms: " + trans + "\tsolve ms:"+ solve + "\t" + sat);
        transtotal += trans;
        solvetotal += solve;
    }

    private static IncrementalSolver synthSolver = null;
    private static Solution execIncrementalSynth(Formula f, Bounds b, SATFactory s) {
        if(synthSolver == null) {
            Options options = new Options();
            options.setSolver(s);
            options.setSymmetryBreaking(0);
            options.setSkolemDepth(-1);
            options.setLogTranslation(0); // changed by TN from 2->0; MUST be 0 to use IncrementalSolver
            options.setBitwidth(8); // [-128,127]
            options.setNoOverflow(true);
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

    private static Solution exec(Formula f, Bounds b, SATFactory s) {
        final Solver solver = new Solver();
        solver.options().setSolver(s);
        solver.options().setSymmetryBreaking(0);
        solver.options().setSkolemDepth(-1);
        solver.options().setLogTranslation(0); // changed by TN from 2->0
        solver.options().setBitwidth(8); // [-128,127]
        solver.options().setNoOverflow(true); // added TN
        return solver.solve(f, b);
    }
}

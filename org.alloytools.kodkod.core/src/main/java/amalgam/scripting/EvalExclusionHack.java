package amalgam.scripting;

import kodkod.ast.*;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.ExprOperator;
import kodkod.engine.Evaluator;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.*;

import java.util.*;
import java.util.function.Predicate;

/**
 * Hacky prototype of 4-part CEGIS synthesis loop for finding initial deployable configurations.
 */
public class EvalExclusionHack {

    final static int loopLimit = 100;
    final static int numStates = 5;
    final static int minInt = -128;
    final static int maxInt = 127;

    final static SATFactory incrementalSolver = SATFactory.MiniSat;
    final static SATFactory coreSolver = SATFactory.MiniSatProver;

    public static void main(String[] args) {
        setupBaseUniverse();
        System.out.println(cegis());
        System.out.println("Time: "+transtotal+" "+solvetotal);
    }

    private static Relation next = Relation.binary("next");
    private static Relation state = Relation.unary("State");
    private static Relation first = Relation.unary("first");
    private static Relation last = Relation.unary("last");
    private static Relation setting = Relation.binary("setting");
    private static Relation next_p = Relation.binary("next_p");
    private static Relation next_target = Relation.binary("next_target");

    private static Relation comfyAt = Relation.binary("comfyAt");
    private static Relation personA = Relation.unary("PersonA");
    private static Relation personB = Relation.unary("PersonB");
    private static Universe universe;
    private static TupleFactory factory;

    // configuration: we have power over the *initial* value of this
    // Thus, synth phase uses a unary relation, and CE phase uses a binary relation.
    // IMPORTANT: we do a lot of string comparison below; make sure config relations have CONF_ in them
    private static Relation canSetCE = Relation.binary("CE_CONF_canSet");
    private static Relation allowedTempCE = Relation.binary("CE_CONF_allowedTemp");
    private static Relation canSetS = Relation.unary("S_CONF_canSet");
    private static Relation allowedTempS = Relation.unary("S_CONF_allowedTemp");

    private static Set<Expression> domain() {
        // Sadly, we can't say "Expression.INTS" because that won't expand.
        // Instead, we have to make it explicit:
        Set<Expression> result = new HashSet<>();
        for(int i=minInt;i<=maxInt;i++) {
            result.add(IntConstant.constant(i).toExpression());
        }
        result.add(personA);
        result.add(personB);
        // TODO: could do this much better, perhaps (even things that are ill-typed will go in the "not" side
        return result;
    }

    private static Formula baseSynthFormula() {
        // Start out with a config that isn't empty...
        Formula tension1 = (canSetS.join(comfyAt)).intersection(allowedTempS).some();
        Variable p = Variable.unary("p");
        // Using forall, anticipating more people eventually
        Formula tension2 = p.join(comfyAt).intersection(allowedTempS).count().gt(IntConstant.constant(1)).forAll(p.oneOf(personA.union(personB)));
        return tension1.and(tension2);
    }

    private static Formula buildPhi() {
        Variable p = Variable.unary("p");
        Variable s = Variable.unary("s");
        return s.join(setting).in(p.join(comfyAt)).forAll(p.oneOf(personA.union(personB))).forAll(s.oneOf(state));
    }

    // TODO: should be an enum, not a pair of booleans. it's modal.
    private static Formula ceFormula(boolean corePhase, boolean corePhasePhi, Solution synthSol) {
        // Concrete starting config = set as bounds

        // We can omit this so long as bounds below force a single specific total ordering on <n> states
        //Formula te = next.totalOrder(state, first, last);

        Variable p = Variable.unary("p");
        Variable s = Variable.unary("s");

        // assertTraceSemantics if NOT providing a concrete trace for core-extraction (phase 2, not 3-4)
        Formula trace;
        Formula structure;
        Formula initial;
        if(!corePhase || !corePhasePhi) {
            // setting, next_p, next_target relations are functional
            // the other config settings are not (might imagine NOBODY being allowed to change temp in a state)
            structure = setting.function(state, Expression.INTS)
                    .and(next_p.function(state, personA.union(personB))) // TODO: person relation
                    .and(next_target.function(state, Expression.INTS));

            // Start in a state where everyone is comfy
            //  all p: Person | s.setting in p.comfyAt    [applied to first]
            initial = first.join(setting).in(p.join(comfyAt)).forAll(p.oneOf(personA.union(personB)));

            // This is a concrete trace of the system
            Formula transition = buildTransition(s, s.join(next));
            trace = transition.forAll(s.oneOf(state.difference(last)));
        } else {
            trace = Formula.TRUE;
            structure = Formula.TRUE;
            initial = Formula.TRUE;
        }

        //  all s: State | all p: Person | s.setting in p.comfyAt
        Formula property = buildPhi();
        Formula modifiedProperty;
        // not in core phase means negate the property to generate a CE
        if(!corePhase) modifiedProperty = property.not();
            // in core phase, but asking for property: asking why did property fail; don't negate
        else if(corePhase && corePhasePhi) modifiedProperty = property;
            // in core phase, NOT asking for property: asking why failure occurred (no prop needed)
        else modifiedProperty = Formula.TRUE;

        // Finally, we need to encode the synthesized initial state
        // (if a config relation is flat, we could just add it in bounds; this is only for
        //  config relations that are stateful!)
        Set<Formula> synthliterals = new HashSet<>();
        if(!corePhase) {
            // efficient version if we're in CE-generation phase
            synthliterals.add(first.join(allowedTempCE).eq(extractSynthExpression(synthSol, allowedTempS)));
            synthliterals.add(first.join(canSetCE).eq(extractSynthExpression(synthSol, canSetS)));
        } else if(corePhasePhi) {
            synthliterals.addAll(desugarInUnion(first.join(allowedTempCE), extractSynthExpression(synthSol, allowedTempS), domain()));
            synthliterals.addAll(desugarInUnion(first.join(canSetCE), extractSynthExpression(synthSol, canSetS), domain()));
        } else {
            // Do nothing; this is a call for the 2-state

            // TODO: really nothing? what if one of the 2 states is the initial state?
        }
        Formula synthInitial = Formula.and(synthliterals);

        return structure.and(initial).and(trace).and(modifiedProperty).and(synthInitial);
    }

    private static Expression extractSynthExpression(Solution synthSol, Relation synthRel) {
        // TODO is there duplicate code here vs. TransitionData?
        Set<Expression> rows = new HashSet<>();
        for(Tuple t : synthSol.instance().relationTuples().get(synthRel)) {
            Set<Expression> cols = new HashSet<>();
            for(int ii = 0; ii<t.arity(); ii++) {
                cols.add(atomToExpression(t.atom(ii)));
            }
            rows.add(Expression.product(cols));
        }
        return Expression.union(rows);
    }

    // The transition predicate on [s, s'] (minus type annotations, beware)
    private static Formula buildTransition(Expression s, Expression s2) {
        return buildTransitionPrim(s.join(setting), s.join(canSetCE), s.join(allowedTempCE),
                s.join(next_p), s.join(next_target),
                s2.join(setting), s2.join(canSetCE), s2.join(allowedTempCE));
    }

    private static Formula buildTransitionPrim(Expression pretemp, Expression preCanSet, Expression preAllowedTemp,
                                               Expression p, Expression targ,
                                               Expression posttemp, Expression postCanSet, Expression postAllowedTemp) {
        // is the temp change permitted? (note these expressions don't have a state attached)
        Formula ante = p.in(preCanSet).and(targ.in(preAllowedTemp));
        Formula thenf = posttemp.eq(targ);
        Formula elsef = posttemp.eq(pretemp);
        Formula settingChange = ante.implies(thenf).and(ante.not().implies(elsef));

        // If try to set to 75 and forbidden...trigger vulnerability
        ante = targ.eq(IntConstant.constant(75).toExpression()).and(ante.not());
        thenf = postAllowedTemp.eq(Expression.INTS).and(postCanSet.eq(personA.union(personB)));
        elsef = postAllowedTemp.eq(preAllowedTemp).and(postCanSet.eq(preCanSet));
        Formula policyChange = ante.implies(thenf).and(ante.not().implies(elsef));
        Formula transition = settingChange.and(policyChange);
        //System.out.println(" ~~~ "+transition);
        return transition;
    }

    private static Expression atomToExpression(Object at) {
        if(at.equals("PersonA")) return personA;
        else if(at.equals("PersonB")) return personB;
        else if(at instanceof Integer) return IntConstant.constant((Integer)at).toExpression();
        else throw new IllegalArgumentException("no person expression built for "+at.toString());
        // TODO: build an atom->expression table so this works more generally
    }

    /**
     * Internal representation for a concrete state transition
     */
    static class TransitionData {
        IntConstant pretemp = null;
        Set<Expression> preCanSet = new HashSet<>();
        Set<Expression> preAllowedTemp = new HashSet<>();

        Expression p = null;
        IntConstant targ = null;

        IntConstant posttemp = null;
        Set<Expression> postCanSet = new HashSet<>();
        Set<Expression> postAllowedTemp = new HashSet<>();

        TransitionData(Solution ce, Object preatom, Object postatom) {
            // Casting/comparisons to null necessary because raw atoms are just Object :-(

            // TODO: duplicate code structure in-method and also vs. ceFormula's extraction from synth
            for(Tuple s : ce.instance().relationTuples().get(canSetCE)) {
                Object sstate = s.atom(0);
                if(sstate.equals(preatom)) {
                    preCanSet.add(atomToExpression(s.atom(1)));
                }
                if(sstate.equals(postatom)) {
                    postCanSet.add(atomToExpression(s.atom(1)));
                }
            }

            for(Tuple s : ce.instance().relationTuples().get(allowedTempCE)) {
                Object sstate = s.atom(0);
                if(sstate.equals(preatom)) {
                    preAllowedTemp.add(atomToExpression(s.atom(1)));
                }
                if(sstate.equals(postatom)) {
                    postAllowedTemp.add(atomToExpression(s.atom(1)));
                }
            }

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
                    p = atomToExpression(pa);
                }
            }
            for(Tuple s : ce.instance().relationTuples().get(next_target)) {
                Object sstate = s.atom(0);
                if (sstate.equals(preatom)) {
                    targ = IntConstant.constant((Integer)s.atom(1));
                }
            }

            if(pretemp == null || p == null || targ == null || posttemp == null)
                throw new IllegalArgumentException("unable to build: ("+pretemp+";"+preCanSet+";"+preAllowedTemp+
                        ")-"+p+";"+targ+"->("+posttemp+";"+postCanSet+";"+postAllowedTemp+")");

        }
    }

    private static Set<Expression> flattenUnion(Expression e) {
        Set<Expression> result = new HashSet<>();
        // base cases
        if(!(e instanceof BinaryExpression) && !(e instanceof NaryExpression)) {
            result.add(e);
            return result;
        }
        if(e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression)e;
            if (!be.op().equals(ExprOperator.UNION)) {
                result.add(e);
                return result;
            }
            // a union to split up
            result.addAll(flattenUnion(be.left()));
            result.addAll(flattenUnion(be.right()));
            return result;
        }
        NaryExpression ne = (NaryExpression)e;
        if(!ne.op().equals(ExprOperator.UNION)) {
            result.add(e);
            return result;
        }
        for(int ii=0;ii<ne.size();ii++) {
            result.addAll(flattenUnion(ne.child(ii)));
        }
        return result;
    }

    private static Set<Formula> desugarInUnion(Expression lhs, Expression rhs, Set<Expression> domain) {
        // Constructed a lhs = rhs expression, where the rhs is a union (possibly nested).
        // Desugar that into a (potentially large) "or" for core purposes
        // ASSUMPTION: lhs is the thing that isnt the union

        Set<Expression> yes = flattenUnion(rhs);
        Set<String> yesStrings = new HashSet<>();
        for(Expression e : yes) {
            yesStrings.add(e.toString());
        }

        // strings again because can't use .equal
        Set<Expression> no = new HashSet<>();
        for(Expression e : domain) {
            if(!yesStrings.contains(e.toString()))
                no.add(e);
        }

        Set<Formula> result = new HashSet<Formula>();
        for(Expression e : yes) {
            result.add(e.in(lhs));
        }
        for(Expression e : no) {
            result.add(e.in(lhs).not());
        }

        //System.out.println("DESUGARING: lhs: "+lhs+"; rhs: "+rhs);
        //System.out.println("AS: "+result);
        //System.out.println("YES was: "+yes);

        return result;
    }

    /*
    private static Formula breakTransition(Solution ce, Object preatom, Object postatom) {
        // Extract pretemp, next_p, next_target, posttemp
        TransitionData tdata = new TransitionData(ce, preatom, postatom);

        return buildTransitionPrim(tdata.pretemp.toExpression(),
                Expression.union(tdata.preCanSet), Expression.union(tdata.preAllowedTemp),
                tdata.p, tdata.targ.toExpression(),
                tdata.posttemp.toExpression(),
                Expression.union(tdata.postCanSet), Expression.union(tdata.postAllowedTemp)).not();
    }

    private static Formula traceExclusion(Solution ce) {
        //ce.instance().relationTuples().get(first) // always State0

        List<Formula> subs = new ArrayList<>();

        // TODO: break initial

        for(Tuple nxt : ce.instance().relationTuples().get(next)) {
            Object pre = nxt.atom(0);
            Object post = nxt.atom(1);

            // Note this isn't just buildTransition(pre, post).not()
            //   because we don't have explicit state atoms to work with at the synth level
            subs.add(breakTransition(ce, pre, post));
        }

        //System.out.println("TE: "+subs);
        // Either first isn't first, or some transition is broken
        return Formula.or(subs);
    }*/

    private static Set<Formula> fixPreTransitionAsFormula(Solution ce, Expression s, boolean includePost, boolean includeAllPost, Set<Formula> negateThese) {
        // s is prestate expression (e.g., first.next.next for 3rd state)
        Evaluator eval = new Evaluator(ce.instance());
        Object pre=null, post=null;
        TupleSet pres = eval.evaluate(s);
        for(Tuple t : pres) {pre = t.atom(0);}
        TupleSet posts = eval.evaluate(s.join(next));
        for(Tuple t : posts) {post = t.atom(0);}
        if(pre == null || post == null) throw new RuntimeException("fixTrace: unable to resolve pre/post: "+pres+"; "+posts);

        Set<Formula> subs = new HashSet<>();

        TransitionData tdata = new TransitionData(ce, pre, post);

        // One sub-subformula for every state relation (pre and post)
        //subs.add(s.join(allowedTempCE).eq(Expression.union(tdata.preAllowedTemp)));
        //subs.add(s.join(next).join(allowedTempCE).eq(Expression.union(tdata.postAllowedTemp)));
        subs.addAll(desugarInUnion(s.join(allowedTempCE), Expression.union(tdata.preAllowedTemp), domain()));
        if(includePost) // handle last
            subs.addAll(desugarInUnion(s.join(next).join(allowedTempCE), Expression.union(tdata.postAllowedTemp), domain()));

        subs.addAll(desugarInUnion(s.join(canSetCE), Expression.union(tdata.preCanSet), domain()));
        if(includePost) // handle last
            subs.addAll(desugarInUnion(s.join(next).join(canSetCE), Expression.union(tdata.postCanSet), domain()));

        // Single setting, no union
        subs.add(s.join(setting).eq(tdata.pretemp.toExpression()));
        if(includePost) // handle last
            subs.add(s.join(next).join(setting).eq(tdata.posttemp.toExpression()));

        // One sub-subformula for event components (no post)
        subs.add(s.join(next_p).eq(tdata.p));
        subs.add(s.join(next_target).eq(tdata.targ.toExpression()));

        ///// Do negation now
        // We've collected all state literals. Now negate as needed.
        // TODO: equals doesn't work; doing the slow thing.
        Set<String> strsNegate = new HashSet<>();
        for(Formula f : negateThese) {
            strsNegate.add(f.toString());
        }
        Set<Formula> toFlip = new HashSet<>();
        for(Formula f: subs) {
            if(strsNegate.contains(f.toString()))
                toFlip.add(f);
        }
        subs.removeAll(toFlip); // this is OK because we switched over to the original objects

        //System.out.println("toFlip: "+toFlip+"; strNegate was: "+strsNegate);
        //System.out.println(subs);
        if(!toFlip.isEmpty()) {
            // Now add the negation of the conjunction of toFlip:
            subs.add(Formula.and(toFlip).not());
        }

        return subs;
    }

    /**
     * Build a formula that expresses a counterexample trace, including values of all state relations and events (Moore style)
     * @param ce The counterexample being expressed as a formula
     * @param negateThese A set of formulas to be negated, if they appear (used by blame-extraction)
     * @param includeStates Build a trace of this many states, including start state
     * @return
     */
    private static Formula fixTraceAsFormula(Solution ce, Set<Formula> negateThese, int includeStates) {
        List<Formula> subs = new ArrayList<>();
        if(numStates < includeStates) throw new RuntimeException("ceBounds called with too many includeStates");
        if(includeStates < 2) throw new RuntimeException("Must have at least two includestates, had "+includeStates);

        // don't do this: assumes the iteration order matches the true ordering!
        //for(Tuple nxt : ce.instance().relationTuples().get(next)) {
        Expression s = first;
        // Loop through all except last:
        for(int iState=1;iState<includeStates;iState++) {
            boolean forceIncludePost = (iState == includeStates-1);
            // s prestate in ce, include everything in poststate even if not negated (but only for last state),
            // negate the conjunction of negateThese
            subs.addAll(fixPreTransitionAsFormula(ce, s, forceIncludePost, true, negateThese));
            s = s.join(next);
        }
        return Formula.and(subs);
    }


    /**
     *
     * @param includeStates indicates how many states to instantiate (up to numStates), for use by blaming via cores.
     *                      Without something like this, following cores can be cyclic. Problem: this strategy won't be
     *                      incremental, since we have to re-translate for every step backward in time.
     * @return
     */
    private static Bounds ceBounds(int includeStates) {
        // Start from synth bounds
        Bounds bounds = synthBounds();

        // Create an explicit trace
        // TODO: exact bound = a weakness in the model, because might miss a shorter trace!
        // if make non-exact, be sure to add containment axioms
        List<Tuple> stateExactly = new ArrayList<>();
        List<Tuple> nextExactly = new ArrayList<>();
        List<Tuple> settingUpper = new ArrayList<>();
        List<Tuple> next_pUpper = new ArrayList<>();
        List<Tuple> next_targetUpper = new ArrayList<>();
        List<Tuple> canSetUpper = new ArrayList<>();
        List<Tuple> allowedTempUpper = new ArrayList<>();

        if(numStates < includeStates) throw new RuntimeException("ceBounds called with bad first/last state");
        if(includeStates < 2) throw new RuntimeException("Must have at least two includestates, had "+includeStates);

        for(int i=0;i<includeStates;i++) {
            stateExactly.add(factory.tuple("State"+i));
            if(i < includeStates-1) {
                nextExactly.add(factory.tuple("State" + i, "State" + (i + 1)));
            }

            next_pUpper.add(factory.tuple("State"+i, "PersonA"));
            next_pUpper.add(factory.tuple("State"+i, "PersonB"));
            for(int j=minInt;j<=maxInt;j++) {
                next_targetUpper.add(factory.tuple("State"+i, j));
                settingUpper.add(factory.tuple("State"+i, j));
            }
            // Don't include synthesized initial config in bounds (see below)
            for(int j=minInt;j<=maxInt;j++) {
                allowedTempUpper.add(factory.tuple("State"+i, j));
            }
            canSetUpper.add(factory.tuple("State"+i, "PersonA"));
            canSetUpper.add(factory.tuple("State"+i, "PersonB"));
        }

        // We could bound the *FIRST* state's configuration here
        // However, since we want to use cores to extract blame in the initial config, we need to assert the
        // last-synthesized initial config as a formula. :-(
        // (Later states can be anything, hence non-exact bound)
        bounds.bound(canSetCE, factory.setOf(canSetUpper));
        bounds.bound(allowedTempCE, factory.setOf(allowedTempUpper));

        bounds.boundExactly(state, factory.setOf(stateExactly));
        bounds.boundExactly(first, factory.setOf(factory.tuple("State0")));
        bounds.boundExactly(last, factory.setOf(factory.tuple("State"+(includeStates-1))));
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
        for(int i=72; i<=75; i++) {
            comfyAts.add(factory.tuple("PersonA", i));
        }
        for(int i=50; i<=100; i++) {
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
        bounds.bound(canSetS, factory.setOf(canSetUpper));
        bounds.bound(allowedTempS, factory.setOf(allowedUpper));
        bounds.boundExactly(personA, factory.setOf(factory.tuple("PersonA")));
        bounds.boundExactly(personB, factory.setOf(factory.tuple("PersonB")));

        // TODO: any issues with diff Tuple objects?
        // Set up integers as integers
        for(int i=minInt; i<=maxInt; i++) {
            bounds.boundExactly(i, factory.setOf(factory.tuple(i)));
        }

        return bounds;
    }

    private static Expression buildStateExpr(int num) {
        // Start at one:
        if(num < 1) throw new RuntimeException("buildStateExpr called with num="+num);
        Expression result = first;
        for(int ii=2;ii<=num;ii++)
            result = result.join(next);
        return result;
    }

    private static int maxTraceLength(Expression e) {
        if(e.equals(first)) return 1;
        if(e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e;
            if(be.right().equals(next)) return 1 + maxTraceLength(be.left());
            return maxTraceLength(be.left()); // e.g., first.next.setting
        }
        return 0;
    }

    private static int maxTraceLength(Formula r) {
        // number of "nexts" following the first, plus one
        if(r instanceof ComparisonFormula) {
            ComparisonFormula cr = (ComparisonFormula) r;
            return Integer.max(maxTraceLength(cr.left()), maxTraceLength(cr.right()));
        } else {
            throw new RuntimeException("maxTraceLength malformed: "+r);
        }

    }

    private static int maxTraceLength(Set<Formula> reasons) {
        int max = 1;
        for(Formula f: reasons) {
            int flen = maxTraceLength(f);
            if(max < flen) max = flen;
        }
        return max;
    }

    private static String cegis() {
        int loopCount = 0;
        Bounds synthbounds = synthBounds();
        Formula synthformula = baseSynthFormula();

        //Collection<Solution> counterexamples = new ArrayList<>();
        while(loopCount++<loopLimit) {
            System.out.println("------------------------- Loop:"+loopCount+"-------------------------");

            ////////////////////////////////////////////////
            // Step 1: synthesize
            Solution sol = execIncrementalSynth(synthformula, synthbounds);
            stats(sol, "synth: ");
            if(sol.sat()) {
                //System.out.println(sol.instance());
                System.out.println(prettyConfigFromSynth(sol));
            }
            else {
                System.out.println(sol.outcome());
                return "Synthesis step failed with UNSAT";
            }

            System.out.println();

            ////////////////////////////////////////////////
            // Step 2: verify
            Bounds cebounds = ceBounds(numStates);
            //System.out.println(cebounds);
            //System.out.println(ceFormula());
            Solution ce =  execNonincrementalCE(ceFormula(false, false, sol), cebounds);
            stats(ce, "verify: ");
            if(ce.unsat()) return "Success in "+loopCount+" iterations!";
            else {
                System.out.println("CE:\n"+ce.instance());
            }

            System.out.println();

            ////////////////////////////////////////////////
            // Step 3: localize trace literals responsible for the property violation (proximate cause)
            // i.e., ask first why the trace violates the property, irrespective of the system transition rules

            // Note on implementation: we can't just add the concrete trace as an exact bound. Then it wouldn't
            //  be used in the core at all, because those variables will be eliminated! instead, encode the trace as a fmla.

            // Include phi, but not system axioms.
            Formula whyFormula = ceFormula(true, true, sol)
            // Also include the entire trace from start to finish.
                    .and(fixTraceAsFormula(ce, new HashSet<>(), numStates));

            Solution why = execNonincrementalCE(whyFormula, cebounds);
            if(why.sat()) {
                System.out.println(); System.out.println(why.instance());
                return "Error: counterexample-why step returned SAT for property on CE trace.";
            }
            // HybridStrategy is giving non-minimal cores, so use RCE
            why.proof().minimize(new RCEStrategy(why.proof().log()));
            Set<Formula> reasons = new HashSet(why.proof().highLevelCore().keySet());
            // Trying new Java8 filter. sadly .equals on the fmla isnt enough, so pretend and use .toString()
            Predicate isAPhi = f -> f.toString().equals(buildPhi().toString());
            reasons.removeIf(isAPhi);
            System.out.println("DEBUG: WHY core: "+reasons);


            ////////////////////////////////////////////////
            // Step 4: find root cause (in initial deployable config) of proximate cause
            // We have a set of "reason" formulas. These may involve multiple states.
            // Ask: why is their conjunction necessary? This loop is set up to seek immediate causes in the prestate,
            // because it's easy to get an unhelpful core that might (e.g.) blame the state *AFTER* the one with the reason.
            // It's also possible to get cores that point to things in the same state. Because of this, we create a problem
            // that fixes the prestate literals but only the (negated) reason literals in the poststate.
            // ^^ TODO

            // Finally, because the set of reasons may involve multiple states, we should be (TODO: not yet done!)
            // starting with the latest reasons, re-sorting every iteration. I believe it's OK to combine reasons
            //  from the same state.


            // TODO: separate solver, single step per invocation? want push/pop!
            // TODO: Can we ever get the initial state literals directly, without iteration?

            Set<Formula> initialReasons = new HashSet<>();
            // until all blame obligations are discharged, keep moving toward initial state
            // TODO: this might loop forever in case of a malformed or anticausal transition function. detect.
            while(!reasons.isEmpty()) {
                System.out.println("Deriving blame for: "+reasons+"; mtl: "+maxTraceLength(reasons));
                // Negate the trace literals we want explained
                int mtl = maxTraceLength(reasons);
                Formula blameFormula = ceFormula(true, false, sol)
                        // Include this prestate (reason -1 depth) and negated reasons
                        .and(fixPreTransitionAsFormula(ce, buildStateExpr(mtl-1), true, false, reasons));
                //System.out.println("blame fmla: "+blameFormula);
                //Bounds blamebounds = ceBounds(mtl); // Later: use mtl to order the blames so we can maintain 2-state bounds
                Bounds blamebounds = ceBounds(2); // include ONLY TWO STATES
                //System.out.println("blame bounds: "+blamebounds);
                Solution blame = execNonincrementalCE(blameFormula, blamebounds);
                if(blame.sat()) {
                    System.out.println();
                    System.out.println(blame.instance());
                    return "Error: counterexample-blame step returned SAT for property on CE trace.";
                }

                // HybridStrategy is producing vastly non-minimal cores on Theo+hack. Use RCE to get guaranteed minimum.
                //blame.proof().minimize(new HybridStrategy(blame.proof().log()));
                blame.proof().minimize(new RCEStrategy(blame.proof().log()));

                HashSet<Formula> localCause = new HashSet<>(blame.proof().highLevelCore().keySet());

                System.out.println("BLAME core (all fmlas): "+localCause);
                // Strip out local causes that aren't trace literals
                HashSet<Formula> toRemove = new HashSet<>();
                for(Formula f: localCause) {
                    // TODO I don't know of a way to do this without instanceof and casting :-(; may need addition to fmla to avoid
                    // Could write a visitor, or record the literal formulas instead?
                    // This will also remove the goal literals, since they are negations, not comparisons
                    if(!(f instanceof ComparisonFormula)) {
                        toRemove.add(f);
                        continue;
                    }
                    // TODO: this is another kludge because of ad-hoc construction of these literal formulas
                    ComparisonFormula cf = (ComparisonFormula) f;
                    if(!cf.op().equals(ExprCompOperator.EQUALS) && !cf.op().equals(ExprCompOperator.SUBSET)) {
                        toRemove.add(f);
                        continue;
                    }

                    if(!cf.toString().contains("CONF_")) {
                        toRemove.add(f);
                        continue;
                    }

                }
                localCause.removeAll(toRemove);

                System.out.println("BLAME core (post filter): "+localCause);

                // Finalize local causes that are about the initial state; add others to reasons and iterate
                reasons.clear();
                for(Formula f: localCause) {
                    // I can't believe I'm doing this...
                    boolean needsMore = f.toString().contains("(first . next)");
                    if(!needsMore) initialReasons.add(f);
                    else reasons.add(f);
                }
            }
            //System.out.println("Final blame set in initial state:"+initialReasons);

            // convert each initial reason from CE (first.rel) to S (rel).
            // TODO: current pipeline can't handle *negated* initial reasons; not sure if failure will be silent
            Set<Formula> initialReasonsS = new HashSet<>();
            for(Formula f : initialReasons) {
                if(!(f instanceof ComparisonFormula)) throw new RuntimeException("Unexpected non-comparison initial-state reason formula: "+f);
                ComparisonFormula cf = (ComparisonFormula) f;
                if(!cf.op().equals(ExprCompOperator.EQUALS) && !cf.op().equals(ExprCompOperator.SUBSET))
                    throw new RuntimeException("Unexpected formula: "+f);
                // Making assumptions about how we created these, but in the absence of a robust substitution visitor
                //     (and .equals/canonicity on Formulas ...)
                Expression relside, valside;
                if(cf.op().equals(ExprCompOperator.EQUALS)) {
                    relside = cf.left(); // first . CE_CONF_allowedTemp = Int[96]+Int[97]
                    valside = cf.right();
                }
                else {
                    relside = cf.right(); // Int[96] in (first . CE_CONF_allowedTemp)
                    valside = cf.left();
                }
                if(relside instanceof BinaryExpression) {
                    BinaryExpression be = (BinaryExpression) relside;
                    if (!(be.op().equals(ExprOperator.JOIN))) throw new RuntimeException("Unexpected formula: " + f);
                    Relation sRel;
                    if (relside.toString().equals(first.join(allowedTempCE).toString())) sRel = allowedTempS;
                    else if (relside.toString().equals(first.join(canSetCE).toString())) sRel = canSetS;
                    else throw new RuntimeException("Unexpected RHS in initial-state reason formula: " + f);
                    initialReasonsS.add(valside.compare(cf.op(), sRel));
                } else
                    throw new RuntimeException("Unexpected initial-state reason formula: "+f);
            }

            System.out.println("Initial state reasons: "+initialReasonsS);
            Formula initialStateCause = Formula.and(initialReasonsS);

            // Step 4: extend synth formula
            // using IncrementalSolver now, so formula is the *delta*
            // Combine trace exclusion with causal information in initial state
            // TODO: trace exclusion is currently lacking the !initial option, which yields unsat. testing blame is isolation for now
            //synthformula = traceExclusion(ce).and(initialStateCause.not());
            synthformula = initialStateCause.not();

            // TODO: issue: core is not breaking down the unions...
            synthbounds = new Bounds(universe); // empty bounds for followup calls to IncrementalSolver
            // To measure performance vs. non-incremental, just restore original fmla/bnds and call normal exec
        }
        return "TIMEOUT: loop limit of "+loopLimit+" exceeded.";
    }

    private static String prettyConfigFromSynth(Solution sol) {
        if(sol.sat()) {
            return "Allowed Temps: " + sol.instance().relationTuples().get(allowedTempS) + " " +
                    "Can Set: " + sol.instance().relationTuples().get(canSetS);
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
    private static Solution execIncrementalSynth(Formula f, Bounds b) {
        if(synthSolver == null) {
            Options options = new Options();
            options.setSolver(incrementalSolver);
            options.setSymmetryBreaking(20);
            options.setSkolemDepth(-1);
            options.setLogTranslation(0); // changed by TN from 2->0; MUST be 0 to use IncrementalSolver
            options.setBitwidth(8); // [-128,127]
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

    private static Solution execNonincrementalCE(Formula f, Bounds b) {
        // TODO (OPT): ideally we could clone copies of a base solver state to avoid re-translation
        //  (indeed, SMT provides this very thing with pop/push)
        // TODO (OPT): trace minimization (iterative deepening? aluminum won't work due to snags)
        final Solver solver = new Solver();
        solver.options().setSolver(coreSolver);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(-1);
        solver.options().setLogTranslation(2);
        solver.options().setCoreGranularity(3); // max = 3
        solver.options().setBitwidth(8); // [-128,127]
        solver.options().setNoOverflow(true); // added TN
        return solver.solve(f, b);
    }
}
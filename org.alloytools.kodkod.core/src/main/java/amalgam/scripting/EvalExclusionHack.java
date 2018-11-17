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
import kodkod.engine.ucore.DynamicRCEStrategy;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.*;

import java.io.IOException;
import java.util.*;
import java.util.function.Predicate;
import java.util.logging.*;

/**
 * Hacky prototype of 4-part CEGIS synthesis loop for finding initial deployable configurations.
 * Exclusion refers to excluding some slice of the potential deployable-initial-config space, NOT trace exclusion.
 */
public class EvalExclusionHack {

    private final static boolean writeLogFile = false; // turn on for debugging
    private final static Logger logger = Logger.getLogger(EvalExclusionHack.class.getName());

    final static int loopLimit = 100;
    final static int numStates = 5;
    final static int minInt =  -128;
    final static int maxInt = 127;

    final static int backdoorTemperature = 75;
    final static int minAComfy = 72;
    final static int maxAComfy = 75;
    final static int minBComfy = 50;
    final static int maxBComfy = 100;

    final static SATFactory incrementalSolver = SATFactory.MiniSat;
    final static SATFactory coreSolver = SATFactory.MiniSatProver;

    private static void output(Level l, String s) {
        if(l.intValue() >= Level.INFO.intValue()) {
            // Print the string if it is INFO or more important
            System.out.println(s);
        }
        if(writeLogFile) {
            logger.log(l, s);
        }
    }
    private static void output(String s) {
        output(Level.INFO, s);
    }

    public static void main(String[] args) throws IOException {
        LogManager.getLogManager().reset(); // disable default handler
        logger.setLevel(Level.ALL);
        FileHandler textHandler = new FileHandler("cegis-log.txt");
        textHandler.setFormatter(new SimpleFormatter());
        logger.addHandler(textHandler);

        long startTime = System.currentTimeMillis();
        setupBaseUniverse();
        output(cegis());
        output("Total time (ms): "+(System.currentTimeMillis()-startTime)+
                ".\nTranslation: "+transtotal+
                ",\nsolve: "+solvetotal+
                ",\ncore minimization (note vulnerable to GC etc.): "+coreMinTotal);
    }

    // Infrastructure relations (same for every problem)
    private static Relation next = Relation.binary("next");
    private static Relation state = Relation.unary("State");
    private static Relation first = Relation.unary("first");
    private static Relation last = Relation.unary("last");

    // Problem-specification relations (there are 2 people, they have comfort ranges)
    // These don't change over time, and they aren't something we synthesize. Take them as input.
    private static Relation comfyAt = Relation.binary("comfyAt");
    private static Relation personA = Relation.unary("PersonA");
    private static Relation personB = Relation.unary("PersonB");

    // Non-deployable configuration. These may be changed by the transition relation, but aren't
    // part of what we synthesize. We may have to take assumptions about these in order to synthesize correctly.
    // (For instance, assume the initial temperature setting isn't something uncomfy.)
    private static Relation setting = Relation.binary("setting");

    // Event relations. Must contain "EVENT_"
    private static Relation next_p = Relation.binary("EVENT_next_p");
    private static Relation next_target = Relation.binary("EVENT_next_target");

    // Deployable configuration: we have power over the *initial* value of these
    // Thus, synth phase uses a unary relation, and CE phase uses a binary relation.
    // IMPORTANT: we do some string comparison below; make sure config relations have CONF_ in them, and
    //   event relations have EVENT_ in them.
    private static Relation canSetCE = Relation.binary("CE_DCONF_canSet");
    private static Relation allowedTempCE = Relation.binary("CE_DCONF_allowedTemp");
    private static Relation canSetS = Relation.unary("S_DCONF_canSet");
    private static Relation allowedTempS = Relation.unary("S_DCONF_allowedTemp");

    private static Universe universe;
    private static TupleFactory factory;

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

    // TODO: these should be replaced by additional properties.
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

    enum CEGISPHASE {SYNTH, COUNTER, PROXIMAL, ROOT};

    // TODO: should use the enum, not a pair of booleans. it's modal.
    private static Formula ceFormula(boolean corePhase, boolean corePhasePhi, Solution synthSol) {
        Variable p = Variable.unary("p");
        Variable s = Variable.unary("s");
        Set<Formula> subs = new HashSet<>();

        // STRUCTURAL CONSTRAINTS and TRANSITION SEMANTICS
        if(!corePhase || !corePhasePhi) {
            // setting, next_p, next_target relations are functional
            // the other config settings are not (might imagine NOBODY being allowed to change temp in a state)
            subs.add(setting.function(state, Expression.INTS));
            subs.add(next_p.function(state, personA.union(personB)));
            subs.add(next_target.function(state, Expression.INTS));

            // This is a concrete trace of the system
            Formula transition = buildTransition(s, s.join(next));
            subs.add(transition.forAll(s.oneOf(state.difference(last))));
        }

        // ASSUMPTIONS: applies to CE generation only:
        if(!corePhase) {
            //  start in a state where everyone is comfy
            //  all p: Person | s.setting in p.comfyAt    [applied to first]
            subs.add(first.join(setting).in(p.join(comfyAt)).forAll(p.oneOf(personA.union(personB))));
        }

        // PROPERTIES: applies to CE and PROXIMAL phases
        //  all s: State | all p: Person | s.setting in p.comfyAt
        Formula property = buildPhi();
        // In COUNTER phase: not in core phase means negate the property to generate a CE
        if(!corePhase) subs.add(property.not());
            // in ROOT phase; asking why did property fail---don't negate
        else if(corePhase && corePhasePhi) subs.add(property);
        // otherwise, in PROXIMAL phase, NOT asking for property: asking why failure occurred (no prop needed)

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

        return Formula.and(subs).and(synthInitial);
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

    // This is a major part of the problem definition: the basic, state-atom-free transition function.
    private static Formula buildTransitionPrim(Expression pretemp, Expression preCanSet, Expression preAllowedTemp,
                                               Expression p, Expression targ,
                                               Expression posttemp, Expression postCanSet, Expression postAllowedTemp) {
        // is the temp change permitted? (note these expressions don't have a state attached)
        Formula ante = p.in(preCanSet).and(targ.in(preAllowedTemp));
        // TEST ANTE: require setting to be an odd number to go through
        //Formula ante = p.in(preCanSet).and(targ.in(preAllowedTemp))
        //        .and(targ.sum().modulo(IntConstant.constant(2)).eq(IntConstant.constant(1)));
                // NOTE: add/sub around max/min can cause issues
        Formula thenf = posttemp.eq(targ);
        Formula elsef = posttemp.eq(pretemp);
        Formula settingChange = ante.implies(thenf).and(ante.not().implies(elsef));

        // If try to set to backdoorTemperature and forbidden...trigger vulnerability
        ante = targ.eq(IntConstant.constant(backdoorTemperature).toExpression()).and(ante.not());
        thenf = postAllowedTemp.eq(Expression.INTS).and(postCanSet.eq(personA.union(personB)));
        elsef = postAllowedTemp.eq(preAllowedTemp).and(postCanSet.eq(preCanSet));
        Formula policyChange = ante.implies(thenf).and(ante.not().implies(elsef));
        Formula transition = settingChange.and(policyChange);
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
        // ASSUME: lhs is the thing that isnt the union

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

        output(Level.FINER, "DESUGARING: lhs: "+lhs+"; rhs: "+rhs+"\n"+
          "AS: "+result+"\n"+
          "YES was: "+yes);

        return result;
    }

    /**
     *
     * @param ce
     * @param s
     * @param includeAllNonNegatedPost
     * @param negateThese Will be included in the negated-conjunct even if not present in the trace; beware
     * @return
     */
    private static Set<Formula> fixPreTransitionAsFormula(Solution ce, Expression s, Expression sInFmlas, boolean includeAllNonNegatedPost, Set<Formula> negateThese) {
        // s is prestate expression (e.g., first.next.next for 3rd state)
        Evaluator eval = new Evaluator(ce.instance());
        Object pre=null, post=null;
        TupleSet pres = eval.evaluate(s);
        for(Tuple t : pres) {pre = t.atom(0);}
        TupleSet posts = eval.evaluate(s.join(next));
        for(Tuple t : posts) {post = t.atom(0);}
        if(pre == null || post == null) throw new RuntimeException("fixTrace: unable to resolve pre/post: "+pres+"; "+posts);

        output(Level.FINER, "fixPreTransitionAsFormula: "+s+"; negate="+negateThese);
        s = null; // force trigger a nasty exception if we build with s below instead of sInFmlas

        Set<Formula> subs = new HashSet<>();
        TransitionData tdata = new TransitionData(ce, pre, post);

        // One sub-subformula for every state relation (pre and post)
        subs.addAll(desugarInUnion(sInFmlas.join(allowedTempCE), Expression.union(tdata.preAllowedTemp), domain()));
        if(includeAllNonNegatedPost) // handle last
            subs.addAll(desugarInUnion(sInFmlas.join(next).join(allowedTempCE), Expression.union(tdata.postAllowedTemp), domain()));

        subs.addAll(desugarInUnion(sInFmlas.join(canSetCE), Expression.union(tdata.preCanSet), domain()));
        if(includeAllNonNegatedPost) // handle last
            subs.addAll(desugarInUnion(sInFmlas.join(next).join(canSetCE), Expression.union(tdata.postCanSet), domain()));

        // Single setting, no union
        subs.add(sInFmlas.join(setting).eq(tdata.pretemp.toExpression()));
        if(includeAllNonNegatedPost) // handle last
            subs.add(sInFmlas.join(next).join(setting).eq(tdata.posttemp.toExpression()));

        // One sub-subformula for event components (no post)
        subs.add(sInFmlas.join(next_p).eq(tdata.p));
        subs.add(sInFmlas.join(next_target).eq(tdata.targ.toExpression()));

        //////////////////////////////////////////////////
        // We've collected all state literals. Now negate as needed.
        // First remove any of toNegate that are present in subs
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

        output(Level.FINER, "toFlip: "+toFlip+"; strNegate was: "+strsNegate+"\nsubs: "+subs);
        if(!negateThese.isEmpty()) {
            // Now add the negation of the conjunction of set to negate:
            subs.add(Formula.and(negateThese).not());
            output(Level.FINER, "negated: "+negateThese);
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
        if(numStates < includeStates) throw new UnsupportedOperationException("ceBounds called with too many includeStates");
        if(includeStates < 2) throw new UnsupportedOperationException("Must have at least two includestates, had "+includeStates);

        // don't do this: assumes the iteration order matches the true ordering!
        //for(Tuple nxt : ce.instance().relationTuples().get(next)) {
        Expression s = first;
        // Loop through all except last:
        for(int iState=1;iState<includeStates;iState++) {
            boolean forceIncludePost = (iState == includeStates-1);
            // s prestate in ce, include everything in poststate even if not negated (but only for last state),
            // negate the conjunction of negateThese
            subs.addAll(fixPreTransitionAsFormula(ce, s, s, forceIncludePost, negateThese));
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

        if(numStates < includeStates) throw new UnsupportedOperationException("ceBounds called with bad first/last state");
        if(includeStates < 2) throw new UnsupportedOperationException("Must have at least two includestates, had "+includeStates);

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
        for(int i=minAComfy; i<=maxAComfy; i++) {
            comfyAts.add(factory.tuple("PersonA", i));
        }
        for(int i=minBComfy; i<=maxBComfy; i++) {
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

        // Set up integers as integers
        for(int i=minInt; i<=maxInt; i++) {
            bounds.boundExactly(i, factory.setOf(factory.tuple(i)));
        }

        return bounds;
    }

    // Build an expression corresponding to the num-th state.
    private static Expression buildStateExpr(int num) {
        // Start at one:
        if(num < 1) throw new UnsupportedOperationException("buildStateExpr called with num="+num);
        Expression result = first;
        for(int ii=2;ii<=num;ii++)
            result = result.join(next);
        return result;
    }

    // Extract the thing being joined onto the end of a first.next.next... expression
    private static Expression findFinalJoin(Expression e) {
        Expression fjoin = null;
        while(e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression)e;
            if(fjoin == null) {
                fjoin = be.right();
                e = be.left();
            }
            else if(be.right().equals(next)) e = be.left();
            else break;
        }
        return fjoin;
    }

    private static Formula rewriteStateLiteralDepth(Formula f, int depth) {
        // recur into the formula, replacing
        Expression replaceWith = buildStateExpr(depth);

        if(f instanceof NotFormula) {
            return rewriteStateLiteralDepth(((NotFormula)f).formula(), depth).not();
        } else if(f instanceof ComparisonFormula) {
            ComparisonFormula cf = (ComparisonFormula) f;
            // TODO duplicate code
            Expression relside, valside;
            if(cf.op().equals(ExprCompOperator.EQUALS)) {
                relside = cf.left(); // first . CE_CONF_allowedTemp = Int[96]+Int[97]
                valside = cf.right();
                output(Level.FINER, "rewriting... relside="+relside+"; valside="+valside+"; final="+findFinalJoin(relside));
                return replaceWith.join(findFinalJoin(relside)).eq(valside);
            }
            else {
                relside = cf.right(); // Int[96] in (first . CE_CONF_allowedTemp)
                valside = cf.left();
                return valside.in(replaceWith.join(findFinalJoin(relside)));
            }

        }
        throw new UnsupportedOperationException("rewriteStateLiteralDepth called with non-negation/comparison: "+f);
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
        if(r instanceof NotFormula) {
            return maxTraceLength(((NotFormula)r).formula());
        }
        // number of "nexts" following the first, plus one
        if(r instanceof ComparisonFormula) {
            ComparisonFormula cr = (ComparisonFormula) r;
            return Integer.max(maxTraceLength(cr.left()), maxTraceLength(cr.right()));
        } else {
            throw new UnsupportedOperationException("maxTraceLength malformed: "+r);
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

    private static Formula removeDoubleNegation(Formula f) {
        if(f instanceof NotFormula) {
            NotFormula nf = (NotFormula) f;
            Formula ff = nf.formula();
            if(ff instanceof NotFormula) {
                NotFormula nnf = (NotFormula) ff;
                return nnf.formula();
            }
            return f;
        }
        return f;
    }

    private static boolean isTraceLiteral(Formula f) {

        // TODO I don't know of a way to do this without instanceof and casting :-(; may need addition to fmla to avoid
        // Could write a visitor, or record the literal formulas instead?
        // This will also remove the goal literals, since they are negations, not comparisons

        if(f instanceof NotFormula) {
            return isTraceLiteral(((NotFormula) f).formula());
        }

        if(!(f instanceof ComparisonFormula)) {
            return false;
        }
        // TODO: this is another kludge because of ad-hoc construction of these literal formulas
        ComparisonFormula cf = (ComparisonFormula) f;
        if(!cf.op().equals(ExprCompOperator.EQUALS) && !cf.op().equals(ExprCompOperator.SUBSET)) {
            return false;
        }

        // Throw out event literals; they aren't useful at this point (kludge; if keeping something we shouldn't, consider
        //   labeling non-deployable configuration and keeping only if deploy/nondeploy relation)
        if(cf.toString().contains("EVENT_")) {
            return false;
        }
        return true;
    }

    private static boolean isOneOfNegated(Formula targ, Set<Formula> fs) {
        for(Formula f: fs) {
            if(f.not().toString().equals(targ.toString()))
                return true; // TODO: strings again
        }
        return false;
    }

    private static String cegis() {
        int loopCount = 0;
        Bounds synthbounds = synthBounds();
        Formula synthformula = baseSynthFormula();

        while(loopCount++<loopLimit) {
            output(Level.INFO, "------------------------- Loop:"+loopCount+"-------------------------");

            ////////////////////////////////////////////////
            // Step 1: synthesize
            Solution sol = execIncrementalSynth(synthformula, synthbounds);
            stats(sol, CEGISPHASE.SYNTH);
            if(sol.sat()) {
                output(Level.INFO, "Candidate: "+prettyConfigFromSynth(sol)+"\n");
            }
            else {
                output(Level.INFO, "synth failed, unsat: "+sol.outcome());
                return "Synthesis step failed with UNSAT";
            }

            ////////////////////////////////////////////////
            // Step 2: verify
            Bounds cebounds = ceBounds(numStates);
            Solution ce =  execNonincrementalCE(ceFormula(false, false, sol), cebounds);
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
            Formula whyCEFormula = ceFormula(true, true, sol);
            // Also include the entire trace from start to finish
            Formula whyTFormula = fixTraceAsFormula(ce, new HashSet<>(), numStates);
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
            Predicate isAPhi = f -> f.toString().equals(buildPhi().toString());
            reasons.removeIf(isAPhi);
            output(Level.INFO, "PROXIMAL CAUSE: "+reasons);


            ////////////////////////////////////////////////
            // Step 4: find root cause (in initial deployable config) of proximate cause
            // We have a set of "reason" formulas. These may involve multiple states.
            // Ask: why is their conjunction necessary? This loop is set up to seek immediate causes in the prestate,
            // because it's easy to get an unhelpful core that might (e.g.) blame the state *AFTER* the one with the reason.
            // It's also possible to get cores that point to things in the same state. Because of this, we create a problem
            // that fixes the prestate literals but only the (negated) reason literals in the poststate.

            /////////////////////
            // Finally, because the set of reasons may involve multiple states, we should be (TODO: not yet done!)
            // starting with the latest reasons, re-sorting every iteration. I believe it's OK to combine reasons
            //  from the same state.
            // Because this isn't done yet, confirm that all reasons have the same mtl:
            int sharedmtl = 0;
            for(Formula f: reasons) {
                if(sharedmtl == 0) sharedmtl = maxTraceLength(f);
                else if(sharedmtl != maxTraceLength(f))
                    throw new UnsupportedOperationException("Proximal cause contained literals with differing state depth (enhancement needed to support more complex properties): "+reasons);
            }
            /////////////////////


            // TODO: separate solver, single step per invocation? want push/pop!
            // TODO: Can we ever get the initial state literals directly, without iteration?

            Set<Formula> initialReasons = new HashSet<>();
            // until all blame obligations are discharged, keep moving toward initial state
            // TODO: this might loop forever in case of a malformed or anticausal transition function. detect.
            while(!reasons.isEmpty()) {
                output(Level.INFO, "Deriving blame for: "+reasons+"; mtl: "+maxTraceLength(reasons));
                int mtl = maxTraceLength(reasons);

                // Because we're limiting ourselves to 2 states, need to rewrite state expressions in reasons.
                Set<Formula> rewrittenReasons = new HashSet<Formula>();
                for(Formula f : reasons) {
                    rewrittenReasons.add(rewriteStateLiteralDepth(f, 2)); // second state
                }
                output(Level.FINER, "Rewritten reasons: "+rewrittenReasons);

                // Negate the trace literals we want explained
                Formula blameCEFormula = ceFormula(true, false, sol);
                // Include this prestate (reason -1 depth) and negated reasons
                Set<Formula> blameTransitionFormula = fixPreTransitionAsFormula(ce, buildStateExpr(mtl-1), first,false, rewrittenReasons);

                Bounds blamebounds = ceBounds(2); // include ONLY TWO STATES
                Solution blame = execNonincrementalCE(blameCEFormula.and(Formula.and(blameTransitionFormula)), blamebounds);
                stats(blame, CEGISPHASE.ROOT);
                if(blame.sat()) {
                    output(Level.INFO, "\n"+blame.instance().relationTuples());
                    return "Error: counterexample-blame step returned SAT for property on CE trace.";
                }

                // HybridStrategy is producing vastly non-minimal cores on Theo+hack. Use RCE to get guaranteed minimum.
                //blame.proof().minimize(new HybridStrategy(blame.proof().log()));
                long beforeCore2 = System.currentTimeMillis();
                blame.proof().minimize(new RCEStrategy(blame.proof().log()));
                // Slower than RCEStrategy for this problem
                //blame.proof().minimize(new DynamicRCEStrategy(blame.proof().log()));
                HashSet<Formula> localCause = new HashSet<>(blame.proof().highLevelCore().keySet());
                coreMinTotal += (System.currentTimeMillis() - beforeCore2);

                output(Level.FINER, "BLAME core (all fmlas, NOT rewritten): "+localCause);
                System.out.println("BLAME core (all fmlas, NOT rewritten): "+localCause);
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

                output(Level.FINER, "BLAME core (post filter): "+localCause);

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
                for(Formula f: localCauseRewritten) {
                    // I can't believe I'm doing this...
                    boolean needsMore = f.toString().contains("(first . next)");
                    if(!needsMore) initialReasons.add(f);
                    else reasons.add(removeDoubleNegation(f));
                }
            }
            output(Level.FINER, "Final blame set in initial state (pre-conversion CE->S):"+initialReasons);

            // convert each initial reason from CE (first.rel) to S (rel).
            // TODO: current pipeline can't handle *negated* initial reasons; not sure if failure will be silent
            Set<Formula> initialReasonsS = new HashSet<>();
            for(Formula f : initialReasons) {
                boolean negated = false;
                if(f instanceof NotFormula) {
                    negated = true;
                    f = ((NotFormula)f).formula();
                }

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
                    Formula reconstructed = valside.compare(cf.op(), sRel);
                    if(negated) reconstructed = reconstructed.not();
                    initialReasonsS.add(reconstructed);
                } else
                    throw new RuntimeException("Unexpected initial-state reason formula: "+f);
            }

            output(Level.INFO, "Initial state reasons: "+initialReasonsS);
            Formula initialStateCause = Formula.and(initialReasonsS);

            // FINALLY: extend synth formula
            // using IncrementalSolver now, so formula is the *delta*
            synthformula = initialStateCause.not();

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

    private static Map<CEGISPHASE, Long> transtotal = new HashMap<>();
    private static Map<CEGISPHASE, Long> solvetotal = new HashMap<>();
    private static long coreMinTotal = 0;
    private static void updateTimeMap(Map<CEGISPHASE, Long> m, CEGISPHASE p, long add) {
        if(!m.keySet().contains(CEGISPHASE.SYNTH)) m.put(CEGISPHASE.SYNTH, Long.valueOf(0));
        if(!m.keySet().contains(CEGISPHASE.COUNTER)) m.put(CEGISPHASE.COUNTER, Long.valueOf(0));
        if(!m.keySet().contains(CEGISPHASE.PROXIMAL)) m.put(CEGISPHASE.PROXIMAL, Long.valueOf(0));
        if(!m.keySet().contains(CEGISPHASE.ROOT)) m.put(CEGISPHASE.ROOT, Long.valueOf(0));

        m.put(p, m.get(p)+add);
    }
    private static void stats(Solution sol, CEGISPHASE phase) {
        // Core minimization time is recorded elsewhere
        String sat = sol.sat() ? "sat" : "unsat";
        long trans = sol.stats().translationTime();
        long solve = sol.stats().solvingTime();
        output(Level.FINE, phase+" trans ms: " + trans + "\tsolve ms: "+ solve + "\t sat: " + sat);
        updateTimeMap(transtotal, phase, trans);
        updateTimeMap(solvetotal, phase, solve);
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


    // In progress: sketching API/problem definitions.
    interface SynthProblem {
        // FOL translation of the temporal goals we have. These should use the CE relations
        Set<Formula> goals();
        // Assumptions (about initial state) like "room always starts at 70 degrees"
        Set<Formula> initialStateAssumptions();
        // Structure, like "this relation is a function" or "A is a subtype of B"
        Set<Formula> structuralAxioms();

        // Relation declarations (use real Relation objects, since we have formulas)
        // suffix of S = without the state column; suffix of CE = with the state column
        Relation stateRelation();
        Set<Relation> helperRelations();
        Set<Relation> deployableRelations();
        Set<Relation> deployableRelationsCE();
        Set<Relation> nondeployableRelationsS();
        Set<Relation> nondeployableRelationsCE();
        Set<Relation> eventRelationsCE();

        // Total size of inputs should be eventRelationsCE.size()+2*(deployableRelationsCE.size()+nondeployableRelationsCE.size())
        Formula buildTransitionPrim(List<Expression> pre, List<Expression> ev, List<Expression> post);

        // CEGIS will need a validator to check, e.g., that eventRelations all contain "EVENT_", that arities match, etc.
    }


}
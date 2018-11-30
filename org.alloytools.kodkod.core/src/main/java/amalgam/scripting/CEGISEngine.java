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

import java.io.IOException;
import java.util.*;
import java.util.function.Predicate;
import java.util.logging.*;

/**
 * Prototype of 4-part CEGIS synthesis loop for finding initial deployable configurations.
 * Exclusion refers to excluding some slice of the potential deployable-initial-config space, NOT trace exclusion.
 */
public class CEGISEngine {

    private final static boolean writeLogFile = false; // turn on for debugging
    private final static Logger logger = Logger.getLogger(CEGISEngine.class.getName());

    final static int loopLimit = 100;
    final static int numStates = 5;
    final static int minInt =  -128;
    final static int maxInt = 127;
    final static int bitwidth = 8;

    private static Universe universe;
    private static TupleFactory factory;

    //SATFactory.LightSAT4J; //SATFactory.DefaultSAT4J; //SATFactory.MiniSat; //SATFactory.Glucose;
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

    public void validate() throws CEGISException {
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

    public static void run(SynthProblem problem) throws CEGISException {
        CEGISEngine cegisSolver = new CEGISEngine(problem);

        long startTime = System.currentTimeMillis();
        output("\n\n===================================================================\nRunning problem: "+problem.desc());

        output(cegisSolver.cegis());
        output("Total time (ms): "+(System.currentTimeMillis()-startTime)+
                ".\nTranslation: "+cegisSolver.transtotal+
                ",\nsolve: "+cegisSolver.solvetotal+
                ",\ncore minimization (note vulnerable to GC etc.): "+cegisSolver.coreMinTotal);
    }

    public static void main(String[] args) throws CEGISException, IOException {
        LogManager.getLogManager().reset(); // disable default handler
        logger.setLevel(Level.ALL);
        FileHandler textHandler = new FileHandler("cegis-log.txt");
        textHandler.setFormatter(new SimpleFormatter());
        logger.addHandler(textHandler);

        run(new OriginalTimTheoHack(minInt, maxInt));
        run(new XLockingDoor(false));
        run(new XLockingDoor(true));
        run(new RoadsAndRoutes(5, 5));
    }

    SynthProblem problem;
    CEGISEngine(SynthProblem problem) throws CEGISException {
        this.problem = problem;
        validate();
        setupBaseUniverse();
    }

    // Infrastructure relations (same for every problem)
    private static Relation state = Relation.unary("State");
    private static Relation enext = Relation.binary("next");
    private static Relation first = Relation.unary("first");
    private static Relation last = Relation.unary("last");

    private static final String STR_FIRSTNEXT = "(first . next)";

    private Set<Expression> domain() {
        // Sadly, we can't say "Expression.INTS" because that won't expand.
        // Instead, we have to make it explicit:
        Set<Expression> result = new HashSet<>();
        for(int i=minInt;i<=maxInt;i++) {
            result.add(IntConstant.constant(i).toExpression());
        }
        for(Relation r : problem.constantSingletonRelations()) {
            result.add(r);
        }

        /* TODO: could do this much better: even things that are ill-typed will be considered by the caller of this
        method, making the set of formulas bigger than it needs to be. */
        return result;
    }

    enum CEGISPHASE {SYNTH, COUNTER, PROXIMAL, ROOT};

    // TODO: should use the enum, not a pair of booleans. it's modal.
    private Formula ceFormula(boolean corePhase, boolean corePhasePhi, Solution synthSol) {
        Variable s = Variable.unary("s");
        Set<Formula> subs = new HashSet<>();

        // STRUCTURAL CONSTRAINTS and TRANSITION SEMANTICS: doesn't apply for proximal-cause generation
        if(!corePhase || !corePhasePhi) {
            // setting, next_p, next_target relations are functional
            // the other config settings are not (might imagine NOBODY being allowed to change temp in a state)
            subs.addAll(problem.structuralAxioms(state));

            // This is a concrete trace of the system
            Formula transition = problem.buildTransition(s, s.join(enext));
            // Consecution from s->s.enext for all except s=last.
            subs.add(transition.forAll(s.oneOf(state.difference(last))));

            // Lasso constraints:
            // (1) lone point that last state progresses to (may not progress if finiteness reqd)
            // TODO: should this stutter instead if no progress is possible?
            Formula loneLoop = last.join(enext).lone();
            // (2) If last does step forward, must obey the transition predicate
            Formula loopObeys = problem.buildTransition(last, last.join(enext));
            subs.add(loneLoop);
            subs.add(loopObeys);
        }

        // ASSUMPTIONS: applies to CE generation only, not core phases
        if(!corePhase) {
            //  start in a state where everyone is comfy,
            subs.addAll(problem.additionalInitialConstraintsP1P2(first));
        }

        // PROPERTIES: applies to CE and PROXIMAL phases
        // TODO: should we break goals down separately? maybe no need to at first
        Formula property = Formula.and(problem.goals(state, enext)); // TODO: enext needs to be "enhanced" enext, with lasso
        // In COUNTER phase: not in core phase means negate the property to generate a CE
        if(!corePhase) subs.add(property.not());
            // in ROOT phase; asking why did property fail---don't negate
        else if(corePhase && corePhasePhi) subs.add(property);
        // otherwise, in PROXIMAL phase, NOT asking for property: asking why failure occurred (no prop needed)

        /////////////////////////////////////////////////////////////////////////////////////////////////////////
        // Encode the synthesized initial state
        // (if a config relation is flat, we could just add it in bounds; this is only for config relations that are stateful!)
        Set<Formula> synthliterals = new HashSet<>();
        if(!corePhase) {
            // efficient version if we're in CE-generation phase
            for(Relation r : problem.deployableRelations()) {
                synthliterals.add(first.join(r).eq(extractSynthExpression(synthSol, r)));
            }
        } else if(corePhasePhi) {
            // inefficient version for blame-generation: need to include the *negative* literals, too.
            for(Relation r : problem.deployableRelations()) {
                synthliterals.addAll(desugarInUnion(first.join(r), extractSynthExpression(synthSol, r), domain()));
            }
        } else {
            // Do nothing; this is a call for the 2-state
        }
        Formula synthInitial = Formula.and(synthliterals);

        return Formula.and(subs).and(synthInitial);
    }

    private Expression extractSynthExpression(Solution synthSol, Relation synthRel) {
        Set<Expression> rows = new HashSet<>();
        for(Tuple t : synthSol.instance().relationTuples().get(synthRel)) {
            Set<Expression> cols = new HashSet<>();
            // Leftmost column is state
            if(!t.atom(0).toString().startsWith("State")) throw new RuntimeException("extractSynthExpression: "+t);
            for(int ii = 1; ii<t.arity(); ii++) {
                cols.add(atomToExpression(t.atom(ii)));
            }
            rows.add(Expression.product(cols));
        }
        if(!rows.isEmpty()) return Expression.union(rows);
        return Expression.NONE; // Expression.union requires non-empty set
    }


    Map<String, Expression> atom2Rel = new HashMap<>();
    private Expression atomToExpression(Object at) {
        if(at instanceof Integer) return IntConstant.constant((Integer)at).toExpression();
        else if(atom2Rel.containsKey(at)) return atom2Rel.get(at);
        else throw new IllegalArgumentException("no expression built for atom "+at.toString());
    }

    /**
     * Internal representation for a concrete state transition
     */
    class TransitionData {
        Solution ce;
        Object preatom;
        Object postatom;

        Map<Relation, Set<Expression>> preValues = new HashMap<>();
        Map<Relation, Set<Expression>> postValues = new HashMap<>();
        Map<Relation, Set<Expression>> evValues = new HashMap<>();

        private void processStateRelation(Relation r) {
            if(r.arity() > 2)
                throw new UnsupportedOperationException("state predicates of arity >2 (w/ state column) currently unsupported");
            for(Tuple s : ce.instance().relationTuples().get(r)) {
                Object sstate = s.atom(0);
                if(sstate.equals(preatom)) {
                    preValues.putIfAbsent(r, new HashSet<>());
                    preValues.get(r).add(atomToExpression(s.atom(1)));
                }
                if(sstate.equals(postatom)) {
                    postValues.putIfAbsent(r, new HashSet<>());
                    postValues.get(r).add(atomToExpression(s.atom(1)));
                }
            }
        }

        private void processEventRelation(Relation r) {
            if(r.arity() > 2)
                throw new UnsupportedOperationException("event predicates of arity >2 (w/ state column) currently unsupported");
            for(Tuple s : ce.instance().relationTuples().get(r)) {
                Object sstate = s.atom(0);
                if (sstate.equals(preatom)) {
                    Object pa = s.atom(1);
                    evValues.putIfAbsent(r, new HashSet<>());
                    evValues.get(r).add(atomToExpression(pa));
                }
            }
        }

        TransitionData(Solution ce, Object preatom, Object postatom) {
            this.ce = ce;
            this.preatom = preatom;
            this.postatom = postatom;

            // Casting/comparisons to null necessary because raw atoms are just Object :-(

            for(Relation sr : problem.deployableRelations()) {
                processStateRelation(sr);
            }
            for(Relation sr : problem.nondeployableRelations()) {
                processStateRelation(sr);
            }
            for(Relation er : problem.eventRelations()) {
                processEventRelation(er);
            }
        }
    }

    private Set<Expression> flattenUnion(Expression e) {
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

    private Set<Formula> desugarInUnion(Expression lhs, Expression rhs, Set<Expression> domain) {
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

        Set<Formula> result = new HashSet<>();
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
    private Set<Formula> fixPreTransitionAsFormula(Solution ce, Expression s, Expression sInFmlas, boolean includeAllNonNegatedPost, Set<Formula> negateThese) {
        // s is prestate expression (e.g., first.enext.enext for 3rd state)
        Evaluator eval = new Evaluator(ce.instance());
        Object pre=null, post=null;
        TupleSet pres = eval.evaluate(s);
        for(Tuple t : pres) {pre = t.atom(0);}
        TupleSet posts = eval.evaluate(s.join(enext));
        for(Tuple t : posts) {post = t.atom(0);}
        if(pre == null || post == null) throw new RuntimeException("fixTrace: unable to resolve pre/post: "+pres+"; "+posts);

        output(Level.FINER, "fixPreTransitionAsFormula: "+s+"; negate="+negateThese);
        s = null; // defensive fail: force trigger a nasty exception if we accidentally build with s below instead of sInFmlas

        Set<Formula> subs = new HashSet<>();
        TransitionData tdata = new TransitionData(ce, pre, post);

        // One sub-subformula for every state relation (pre and post)
        for(Relation r : problem.nondeployableRelations()) {
            subs.addAll(desugarInUnion(sInFmlas.join(r), Expression.union(tdata.preValues.get(r)), domain()));
            if(includeAllNonNegatedPost) // handle last
                subs.addAll(desugarInUnion(sInFmlas.join(enext).join(r), Expression.union(tdata.postValues.get(r)), domain()));
        }
        for(Relation r : problem.deployableRelations()) {
            subs.addAll(desugarInUnion(sInFmlas.join(r), Expression.union(tdata.preValues.get(r)), domain()));
            if(includeAllNonNegatedPost) // handle last
                subs.addAll(desugarInUnion(sInFmlas.join(enext).join(r), Expression.union(tdata.postValues.get(r)), domain()));
        }

        // One sub-subformula for event components (no post)
        for(Relation r : problem.eventRelations()) {
            subs.add(sInFmlas.join(r).eq(Expression.union(tdata.evValues.get(r))));
        }

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
    private Formula fixTraceAsFormula(Solution ce, Set<Formula> negateThese, int includeStates) {
        List<Formula> subs = new ArrayList<>();
        if(numStates < includeStates) throw new UnsupportedOperationException("fixTraceAsFormula called with too many includeStates");
        if(includeStates < 2) throw new UnsupportedOperationException("Must have at least two includestates, had "+includeStates);

        // don't do this: assumes the iteration order matches the true ordering!
        //for(Tuple nxt : ce.instance().relationTuples().get(enext)) {
        Expression s = first;
        // Loop through all except last:
        for(int iState=1;iState<includeStates;iState++) {
            boolean forceIncludePost = (iState == includeStates-1);
            // s prestate in ce, include everything in poststate even if not negated (but only for last state),
            // negate the conjunction of negateThese
            subs.addAll(fixPreTransitionAsFormula(ce, s, s, forceIncludePost, negateThese));
            s = s.join(enext);
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
    private Bounds buildBounds(int includeStates) {
        if(numStates < includeStates) throw new UnsupportedOperationException("buildBounds called with bad first/last state");
        if(includeStates < 1) throw new UnsupportedOperationException("Must have at least one includestate, had "+includeStates);

        Bounds bounds = new Bounds(universe);

        // Set up integers as integers (this is the way Alloy does it)
        for(int i=minInt; i<=maxInt; i++) {
            bounds.boundExactly(i, factory.setOf(factory.tuple(i)));
        }

        // Create an explicit trace (if only one includeStates, we're doing initial synthesis, not really a "trace")
        // TODO: exact bound = a weakness in the model, because might miss a shorter trace!
        // TODO: add lasso cycle point as another singleton unary relation, require transition (in fmlas)
        // if make non-exact, be sure to add containment axioms
        List<Tuple> stateExactly = new ArrayList<>();
        List<Tuple> nextUpper = new ArrayList<>();
        List<Tuple> nextLower = new ArrayList<>();

        String lastAtom = "State"+(includeStates-1);

        // Bound the state infrastructure, but defer the rest to the problem
        for(int i=0;i<includeStates;i++) {
            stateExactly.add(factory.tuple("State" + i));
            if (i < includeStates - 1) {
                nextUpper.add(factory.tuple("State" + i, "State" + (i + 1)));
                nextLower.add(factory.tuple("State" + i, "State" + (i + 1)));
            }
            // Add "enhanced" enext bounds: permit lasso if numStates > 1
            if(includeStates > 1)
                nextUpper.add(factory.tuple(lastAtom, "State"+i)); // might loop back here
        }
        bounds.boundExactly(state, factory.setOf(stateExactly));
        bounds.boundExactly(first, factory.setOf(factory.tuple("State0")));
        bounds.boundExactly(last, factory.setOf(factory.tuple(lastAtom)));
        if(!nextUpper.isEmpty()) {
            bounds.bound(enext, factory.setOf(nextLower), factory.setOf(nextUpper));
        } else {
            bounds.boundExactly(enext, factory.noneOf(2));
        }

        problem.setBounds(bounds, stateExactly);
        return bounds;
    }

    // The CEGIS engine must do this, not the SynthProblem, since the engine is responsible for the state abstraction.
    private void setupBaseUniverse() {
        // Universe
        List<Object> atoms = new ArrayList<>();
        for(Relation r : problem.constantSingletonRelations()) {
            atoms.add(r.name());
            atom2Rel.put(r.name(), r);
        }

        // Add atoms for each integer. This is the way Alloy->Kodkod does it.
        for(int i=minInt; i<=maxInt; i++) {
            atoms.add(Integer.valueOf(i));
        }
        for(int i=0;i<numStates;i++) {
            atoms.add("State" + i);
        }

        universe = new Universe(atoms);
        factory = universe.factory();
    }

    // Build an expression corresponding to the num-th state.
    private Expression buildStateExpr(int num) {
        // Start at one:
        if(num < 1) throw new UnsupportedOperationException("buildStateExpr called with num="+num);
        Expression result = first;
        for(int ii=2;ii<=num;ii++)
            result = result.join(enext);
        return result;
    }

    // Extract the thing being joined onto the end of a first.enext.enext... expression
    private Expression findFinalJoin(Expression e) {
        Expression fjoin = null;
        while(e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression)e;
            if(fjoin == null) {
                fjoin = be.right();
                e = be.left();
            }
            else if(be.right().equals(enext)) e = be.left();
            else break;
        }
        return fjoin;
    }

    private Formula rewriteStateLiteralDepth(Formula f, int depth) {
        // recur into the formula, replacing
        Expression replaceWith = buildStateExpr(depth);

        if(f instanceof NotFormula) {
            return rewriteStateLiteralDepth(((NotFormula)f).formula(), depth).not();
        } else if(f instanceof ComparisonFormula) {
            ComparisonFormula cf = (ComparisonFormula) f;
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

    private int maxTraceLength(Expression e) {
        if(e.equals(first)) return 1;
        if(e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e;
            if(be.right().equals(enext)) return 1 + maxTraceLength(be.left());
            return maxTraceLength(be.left()); // e.g., first.enext.setting
        }
        return 0;
    }
    private int maxTraceLength(Formula r) {
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
    private int maxTraceLength(Set<Formula> reasons) {
        int max = 1;
        for(Formula f: reasons) {
            int flen = maxTraceLength(f);
            if(max < flen) max = flen;
        }
        return max;
    }

    private Formula removeDoubleNegation(Formula f) {
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

    private boolean isTraceLiteral(Formula f) {

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

    private boolean isOneOfNegated(Formula targ, Set<Formula> fs) {
        for(Formula f: fs) {
            if(f.not().toString().equals(targ.toString()))
                return true; // TODO: strings again
        }
        return false;
    }

    private String cegis() {
        int loopCount = 0;
        Bounds synthbounds = buildBounds(1);
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
            Bounds cebounds = buildBounds(numStates);
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
                Formula blameCEFormula = ceFormula(true, false, sol);
                // Include this prestate (reason -1 depth) and negated reasons
                Set<Formula> blameTransitionFormula = fixPreTransitionAsFormula(ce, buildStateExpr(mtl-1), first,false, rewrittenReasons);

                Bounds blamebounds = buildBounds(2); // include ONLY TWO STATES
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

            synthbounds = new Bounds(universe); // empty bounds for followup calls to IncrementalSolver
            // To measure performance vs. non-incremental, just restore original fmla/bnds and call normal exec
        }
        return "TIMEOUT: loop limit of "+loopLimit+" exceeded.";
    }

    private Map<CEGISPHASE, Long> transtotal = new HashMap<>();
    private Map<CEGISPHASE, Long> solvetotal = new HashMap<>();
    private long coreMinTotal = 0;
    private void updateTimeMap(Map<CEGISPHASE, Long> m, CEGISPHASE p, long add) {
        if(!m.keySet().contains(CEGISPHASE.SYNTH)) m.put(CEGISPHASE.SYNTH, Long.valueOf(0));
        if(!m.keySet().contains(CEGISPHASE.COUNTER)) m.put(CEGISPHASE.COUNTER, Long.valueOf(0));
        if(!m.keySet().contains(CEGISPHASE.PROXIMAL)) m.put(CEGISPHASE.PROXIMAL, Long.valueOf(0));
        if(!m.keySet().contains(CEGISPHASE.ROOT)) m.put(CEGISPHASE.ROOT, Long.valueOf(0));

        m.put(p, m.get(p)+add);
    }

    private void stats(Solution sol, CEGISPHASE phase) {
        // Core minimization time is recorded elsewhere
        String sat = sol.sat() ? "sat" : "unsat";
        long trans = sol.stats().translationTime();
        long solve = sol.stats().solvingTime();
        output(Level.FINE, phase+" trans ms: " + trans + "\tsolve ms: "+ solve + "\t sat: " + sat);
        updateTimeMap(transtotal, phase, trans);
        updateTimeMap(solvetotal, phase, solve);
    }

    private IncrementalSolver synthSolver = null;
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
package amalgam;

import kodkod.ast.*;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.instance.*;

import java.util.*;
import java.util.logging.Level;

import static amalgam.Logger.*;
import static amalgam.CEGISHelpers.*;

/**
 * Given a synth problem, constructs the basis the CEGIS engine loops over
 */
public class CEGISBase {
    private SynthProblem problem;
    public Universe universe;
    private TupleFactory factory;
    private Map<String, Expression> atom2Rel = new HashMap<>();

    /**
     * TODO
     * The CEGIS engine must do this, not the SynthProblem, since the engine is responsible for the state abstraction.
     * @param problem
     */
    public CEGISBase(SynthProblem problem) {
        this.problem = problem;
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

    /**
     * TODO
     * @param at
     * @return
     */
    public Expression atomToExpression(Object at) throws CEGISException {
        if(at instanceof Integer) return IntConstant.constant((Integer)at).toExpression();
        else if(atom2Rel.containsKey(at)) return atom2Rel.get(at);
        else throw new CEGISException("Tried to convert atom to expression, but no integer or "+
                    "declared constant expression found for atom: "+at);
    }

    /**
     * TODO
     * @param t Tuple to convert to expression (leftmost column is ignored and assumed to be State)
     * @return an Expression for this tuple (via constant relations, ints, etc.)
     * @throws CEGISException
     */
    public Expression tupleToExpressionSkipLeftmost(Tuple t) throws CEGISException {
        if(!t.atom(0).toString().contains("State"))
            throw new CEGISException("Tried call tupleToExpressionSkipLeftmost on non-stateful tuple: "+t);
        if(t.arity() < 2)
            throw new CEGISException("Tried call tupleToExpressionSkipLeftmost on tuple with arity <2: "+t);
        List<Expression> cols = new ArrayList<>(t.arity()-1);
        for(int ii=1;ii<t.arity();ii++) { // ignore the state atom
            cols.add(atomToExpression(t.atom(ii)));
        }
        return Expression.product(cols);
    }

    /**
     * TODO
     * @param r a stateful relation (leftmost column will be ignored!)
     * @param bounds bounds object, used to provide actual domain
     * @return set of expressions in the upper bound of r
     */
    public Set<Expression> buildDomain(Relation r, Bounds bounds) throws CEGISException {
        // Sadly, we can't say "Expression.INTS" because that won't expand.
        // Instead, we have to make it explicit:
        Set<Expression> result = new HashSet<>();

        // For everything in the upper bound of r, find its associated expression. If none found, problem is ill-formed.
        for(Tuple t : bounds.upperBound(r)) {
            result.add(tupleToExpressionSkipLeftmost(t));
        }

        return result;
    }

    /**
     * TODO
     * @param includeStates indicates how many states to instantiate (up to numStates), for use by blaming via cores.
     *                      Without something like this, following cores can be cyclic. Problem: this strategy won't be
     *                      incremental, since we have to re-translate for every step backward in time.
     * @return
     */
    public Bounds buildBounds(int includeStates) {
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

    /**
     * Build a formula that expresses a counterexample trace, including values of all state relations and events (Moore style)
     * @param ce The counterexample being expressed as a formula
     * @param negateThese A set of formulas to be negated, if they appear (used by blame-extraction)
     * @param includeStates Build a trace of this many states, including start state
     * @return
     */
    public Formula fixTraceAsFormula(Solution ce, Bounds bounds, Set<Formula> negateThese, int includeStates) throws CEGISException {
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
            subs.addAll(fixPreTransitionAsFormula(ce, bounds, s, s, forceIncludePost, negateThese));
            s = s.join(enext);
        }
        return Formula.and(subs);
    }

    /**
     * TODO
     * @param ce
     * @param bounds
     * @param s
     * @param includeAllNonNegatedPost
     * @param negateThese Will be included in the negated-conjunct even if not present in the trace; beware
     * @return
     */
    public Set<Formula> fixPreTransitionAsFormula(Solution ce, Bounds bounds, Expression s, Expression sInFmlas,
                                                  boolean includeAllNonNegatedPost, Set<Formula> negateThese)
    throws CEGISException {
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
        CEGISTransition tdata = new CEGISTransition(ce, pre, post, problem, this);

        // One sub-subformula for every state relation (pre and post)
        for(Relation r : problem.nondeployableRelations()) {
            subs.addAll(desugarInUnion(sInFmlas.join(r), Expression.union(tdata.preValues.get(r)), buildDomain(r, bounds)));
            if(includeAllNonNegatedPost) // handle last
                subs.addAll(desugarInUnion(sInFmlas.join(enext).join(r), Expression.union(tdata.postValues.get(r)), buildDomain(r, bounds)));
        }
        for(Relation r : problem.deployableRelations()) {
            subs.addAll(desugarInUnion(sInFmlas.join(r), Expression.union(tdata.preValues.get(r)), buildDomain(r, bounds)));
            if(includeAllNonNegatedPost) // handle last
                subs.addAll(desugarInUnion(sInFmlas.join(enext).join(r), Expression.union(tdata.postValues.get(r)), buildDomain(r, bounds)));
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
     * TODO
     * @param corePhase
     * @param corePhasePhi
     * @param synthSol
     * @return
     */
    public Formula ceFormula(Bounds bounds, boolean corePhase, boolean corePhasePhi, Solution synthSol) throws CEGISException {
        // TODO: should use the enum, not a pair of booleans. it's modal.
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
                synthliterals.addAll(desugarInUnion(first.join(r), extractSynthExpression(synthSol, r), buildDomain(r, bounds)));
            }
        } else {
            // Do nothing; this is a call for the 2-state
        }
        Formula synthInitial = Formula.and(synthliterals);
        return Formula.and(subs).and(synthInitial);
    }

    /**
     * TODO
     * @param synthSol
     * @param synthRel
     * @return
     */
    public Expression extractSynthExpression(Solution synthSol, Relation synthRel) throws CEGISException {
        Set<Expression> rows = new HashSet<>();
        for(Tuple t : synthSol.instance().relationTuples().get(synthRel)) {
            rows.add(tupleToExpressionSkipLeftmost(t));
        }
        if(!rows.isEmpty()) return Expression.union(rows);

        // No rows but Expression.union requires non-empty set. Need to construct a NONE expression of correct arity.
        Expression none = Expression.NONE; // 0th column was state; start for 1th column
        for(int ii=2;ii<synthRel.arity();ii++) // for 2th ++ column
            none = none.product(Expression.NONE);
        return none;
    }
}

package amalgam.cegis;

import kodkod.ast.Expression;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.instance.Tuple;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Internal representation for a concrete state transition
 */
class Transition {
    private Solution ce;
    private Object prestateatom;
    private Object poststateatom;
    Map<Relation, Set<Expression>> preValues = new HashMap<>();
    Map<Relation, Set<Expression>> postValues = new HashMap<>();
    Map<Relation, Set<Expression>> evValues = new HashMap<>();

    /**
     * TODO
     * @param ce
     * @param prestateatom
     * @param poststateatom
     * @param problem
     * @param base
     */
    Transition(Solution ce, Object prestateatom, Object poststateatom, Problem problem, Base base) throws CEGISException {
        this.ce = ce;
        this.prestateatom = prestateatom;
        this.poststateatom = poststateatom;
        // Casting/comparisons to null necessary because raw atoms are just Object :-(
        for(Relation sr : problem.deployableRelations()) {
            preValues.putIfAbsent(sr, new HashSet<>()); // may be no tuples, so create here, not inside processStateRelation
            postValues.putIfAbsent(sr, new HashSet<>());
            processStateRelation(sr, base);
        }
        for(Relation sr : problem.nondeployableRelations()) {
            preValues.putIfAbsent(sr, new HashSet<>()); // may be no tuples, so create here, not inside processStateRelation
            postValues.putIfAbsent(sr, new HashSet<>());
            processStateRelation(sr, base);
        }
        for(Relation er : problem.eventRelations()) {
            evValues.putIfAbsent(er, new HashSet<>()); // may be no tuples, so create here, not inside processStateRelation
            processEventRelation(er, base);
        }
    }

    /**
     * TODO
     * @param r
     * @param base
     */
    private void processStateRelation(Relation r, Base base) throws CEGISException {
        if(r.arity() > 2)
            throw new UnsupportedOperationException("state predicates of arity >2 (w/ state column) currently unsupported");
        for(Tuple s : ce.instance().relationTuples().get(r)) {
            Object sstate = s.atom(0);
            if(sstate.equals(prestateatom)) {
                preValues.get(r).add(base.buildTupleAsExpression(s));
            }
            if(sstate.equals(poststateatom)) {
                postValues.get(r).add(base.buildTupleAsExpression(s));
            }
        }
    }

    /**
     * TODO
     * @param r
     * @param base
     */
    private void processEventRelation(Relation r, Base base) throws CEGISException {
        if(r.arity() > 2)
            throw new UnsupportedOperationException("event predicates of arity >2 (w/ state column) currently unsupported");
        for(Tuple s : ce.instance().relationTuples().get(r)) {
            Object sstate = s.atom(0);
            if (sstate.equals(prestateatom)) {
                evValues.get(r).add(base.buildTupleAsExpression(s));
            }
        }
    }
}

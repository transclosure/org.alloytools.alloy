package amalgam;

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
public class CEGISTransition {
    private Solution ce;
    private Object prestateatom;
    private Object poststateatom;
    public Map<Relation, Set<Expression>> preValues = new HashMap<>();
    public Map<Relation, Set<Expression>> postValues = new HashMap<>();
    public Map<Relation, Set<Expression>> evValues = new HashMap<>();

    /**
     * TODO
     * @param ce
     * @param prestateatom
     * @param poststateatom
     * @param problem
     * @param base
     */
    public CEGISTransition(Solution ce, Object prestateatom, Object poststateatom, SynthProblem problem, CEGISBase base) throws CEGISException {
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
    private void processStateRelation(Relation r, CEGISBase base) throws CEGISException {
        if(r.arity() > 2)
            throw new UnsupportedOperationException("state predicates of arity >2 (w/ state column) currently unsupported");
        for(Tuple s : ce.instance().relationTuples().get(r)) {
            Object sstate = s.atom(0);
            if(sstate.equals(prestateatom)) {
                preValues.get(r).add(base.tupleToExpressionSkipLeftmost(s));
            }
            if(sstate.equals(poststateatom)) {
                postValues.get(r).add(base.tupleToExpressionSkipLeftmost(s));
            }
        }
    }

    /**
     * TODO
     * @param r
     * @param base
     */
    private void processEventRelation(Relation r, CEGISBase base) throws CEGISException {
        if(r.arity() > 2)
            throw new UnsupportedOperationException("event predicates of arity >2 (w/ state column) currently unsupported");
        for(Tuple s : ce.instance().relationTuples().get(r)) {
            Object sstate = s.atom(0);
            if (sstate.equals(prestateatom)) {
                evValues.get(r).add(base.tupleToExpressionSkipLeftmost(s));
            }
        }
    }
}

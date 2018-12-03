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
    private Object preatom;
    private Object postatom;
    public Map<Relation, Set<Expression>> preValues = new HashMap<>();
    public Map<Relation, Set<Expression>> postValues = new HashMap<>();
    public Map<Relation, Set<Expression>> evValues = new HashMap<>();

    /**
     * TODO
     * @param ce
     * @param preatom
     * @param postatom
     * @param problem
     * @param base
     */
    public CEGISTransition(Solution ce, Object preatom, Object postatom, SynthProblem problem, CEGISBase base) {
        this.ce = ce;
        this.preatom = preatom;
        this.postatom = postatom;
        // Casting/comparisons to null necessary because raw atoms are just Object :-(
        for(Relation sr : problem.deployableRelations()) {
            processStateRelation(sr, base);
        }
        for(Relation sr : problem.nondeployableRelations()) {
            processStateRelation(sr, base);
        }
        for(Relation er : problem.eventRelations()) {
            processEventRelation(er, base);
        }
    }

    /**
     * TODO
     * @param r
     * @param base
     */
    private void processStateRelation(Relation r, CEGISBase base) {
        if(r.arity() > 2)
            throw new UnsupportedOperationException("state predicates of arity >2 (w/ state column) currently unsupported");
        for(Tuple s : ce.instance().relationTuples().get(r)) {
            Object sstate = s.atom(0);
            if(sstate.equals(preatom)) {
                preValues.putIfAbsent(r, new HashSet<>());
                preValues.get(r).add(base.atomToExpression(s.atom(1)));
            }
            if(sstate.equals(postatom)) {
                postValues.putIfAbsent(r, new HashSet<>());
                postValues.get(r).add(base.atomToExpression(s.atom(1)));
            }
        }
    }

    /**
     * TODO
     * @param r
     * @param base
     */
    private void processEventRelation(Relation r, CEGISBase base) {
        if(r.arity() > 2)
            throw new UnsupportedOperationException("event predicates of arity >2 (w/ state column) currently unsupported");
        for(Tuple s : ce.instance().relationTuples().get(r)) {
            Object sstate = s.atom(0);
            if (sstate.equals(preatom)) {
                Object pa = s.atom(1);
                evValues.putIfAbsent(r, new HashSet<>());
                evValues.get(r).add(base.atomToExpression(pa));
            }
        }
    }
}

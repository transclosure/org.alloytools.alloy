package amalgam.scripting;

import kodkod.ast.*;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;

import java.util.*;

/**
 * Unsatisfiable synthesis problem involving an "X" safety property.
 * One config var: is the door open or closed?
 * We control the initial value of the door, but people can open/close it at will.
 * Property: G(open -> X closed)   ...which is entirely out of our control.
 */
public class XUnsat implements SynthProblem {

    private int minInt;
    private int maxInt;

    XUnsat(int minInt, int maxInt) {
        this.minInt = minInt;
        this.maxInt = maxInt;
    }

    // Event relations. Must contain "EVENT_"
    private static Relation next_door = Relation.binary("EVENT_next_door");

    // Deployable configuration: we have power over the *initial* value of these
    private static Relation door = Relation.binary("DCONF_door");

    // Booleans
    private static Relation bTrue = Relation.unary("TRUE");
    private static Relation bFalse = Relation.unary("FALSE");

    @Override
    public Set<Formula> goals(Relation stateDomain, Expression enext) {
        Variable s = Variable.unary("s");
        Formula prop = bTrue.in(s.join(door)).implies(bFalse.in(s.join(enext).join(door))).forAll(s.oneOf(stateDomain));
        return Collections.singleton(prop); // immutable
    }

    @Override
    public Set<Formula> additionalInitialConstraintsP1P2(Expression first) {
        Set<Formula> result = new HashSet<>();
        return result;
    }

    @Override
    public Formula buildTransition(Expression s, Expression s2) {
        Formula transition = s2.join(door).eq(s.join(next_door));
        return transition;
    }

    @Override
    public Set<Formula> structuralAxioms(Expression state) {
        Set<Formula> subs = new HashSet<>();
        subs.add(door.function(state, bTrue.union(bFalse)));
        return subs;
    }

    @Override
    public Set<Relation> helperRelations() {
        Set<Relation> result = new HashSet<>();
        return result;
    }

    @Override
    public Set<Relation> deployableRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(door);
        return result;
    }

    @Override
    public Set<Relation> nondeployableRelations() {
        Set<Relation> result = new HashSet<>();
        return result;
    }

    @Override
    public Set<Relation> eventRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(next_door);
        return result;
    }

    @Override
    public Set<Relation> constantSingletonRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(bTrue);
        result.add(bFalse);
        return result;
    }

    @Override
    public String prettyConfigFromSynth(Solution sol) {
        if(sol.sat()) {
            return "Door: " + sol.instance().relationTuples().get(door);
        } else {
            return "UNSAT";
        }
    }

    @Override
    public void setBounds(Bounds bounds, Collection<Tuple> stateExactly) {
        TupleFactory factory = bounds.universe().factory();

        List<Tuple> next_doorUpper = new ArrayList<>();
        List<Tuple> doorUpper = new ArrayList<>();

        for(Tuple st: stateExactly) {
            next_doorUpper.add(st.product(factory.tuple("TRUE")));
            next_doorUpper.add(st.product(factory.tuple("FALSE")));
            doorUpper.add(st.product(factory.tuple("TRUE")));
            doorUpper.add(st.product(factory.tuple("FALSE")));

        }

        bounds.bound(door, factory.setOf(doorUpper));
        bounds.bound(next_door, factory.setOf(next_doorUpper));
        bounds.boundExactly(bTrue, factory.setOf(factory.tuple("TRUE")));
        bounds.boundExactly(bFalse, factory.setOf(factory.tuple("FALSE")));
    }

    @Override
    public String desc() {
        return "door open/close with open->Xclosed. unsat.";
    }
}

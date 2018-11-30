package amalgam.scripting;

import kodkod.ast.*;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;

import java.util.*;

/**
 * Unsatisfiable synthesis problem involving an "X" safety property.
 * Two config vars:
 *   (1) is the door open or closed?
 *   (2) is the door locked?
 * People can (try to) open/close the door at will.
 * Once the door is closed, if it's locked, it can't be reopened or unlocked.
 * Property: G(trying-to-open -> X opened)
 * Expect to deduce door must be unlocked.
 */
public class XLockingDoor implements SynthProblem {

    private boolean flipSignOfUnlocked;

    /**
     * Initialize an instance of this problem.
     * @param flipSignOfUnlocked Different solvers/computers may find different first initial configurations.
     *                         Since we want this to be a *TEST*, we need to make sure CEGIS doesn't terminate
     *                         after one iteration (as it will if the door starts unlocked).
     *                         Flip the value of this boolean (or try both) to make sure this test actually tests.
     */
    XLockingDoor(boolean flipSignOfUnlocked) {
        this.flipSignOfUnlocked = flipSignOfUnlocked;
    }

    Expression isUnlocked() {
        if(!flipSignOfUnlocked) return bTrue; // unlocked? yes
        return bFalse;  // !unlocked? no
    }

    // Event relations. Must contain "EVENT_"
    private static Relation next_door = Relation.binary("EVENT_next_door");

    // Deployable configuration: we have power over the *initial* value of these
    private static Relation doorOpen = Relation.binary("DCONF_doorOpen");
    private static Relation doorUnlocked = Relation.binary("DCONF_doorUnlocked");

    // Booleans
    private static Relation bTrue = Relation.unary("TRUE");
    private static Relation bFalse = Relation.unary("FALSE");

    @Override
    public Set<Formula> goals(Relation stateDomain, Expression enext) {
        Variable s = Variable.unary("s");
        // If the user is trying to open the door, it'l be open in next state
        Formula prop = bTrue.in(s.join(next_door)).implies(bTrue.in(s.join(enext).join(doorOpen))).forAll(s.oneOf(stateDomain));
        return Collections.singleton(prop); // immutable
    }

    @Override
    public Set<Formula> additionalInitialConstraintsP1P2(Expression first) {
        Set<Formula> result = new HashSet<>();
        return result;
    }

    @Override
    public Formula buildTransition(Expression s, Expression s2) {
        Formula islocked = isUnlocked().in(s.join(doorUnlocked)).not();
        Formula allowed = islocked.not().or(bTrue.in(s.join(doorOpen)));
        // If unlocked or open, allow the user to do whatever
        Formula transition1 = allowed.implies(s2.join(doorOpen).eq(s.join(next_door)));
        // If locked and closed, nothing changes
        Formula transition2 = allowed.not().implies(s2.join(doorOpen).eq(s.join(doorOpen)));
        // Locked/Unlocked can't be changed
        Formula lockedConstant = s2.join(doorUnlocked).eq(s.join(doorUnlocked));
        return transition1.and(transition2).and(lockedConstant);
    }

    @Override
    public Set<Formula> structuralAxioms(Expression state) {
        Set<Formula> subs = new HashSet<>();
        subs.add(doorOpen.function(state, bTrue.union(bFalse)));
        subs.add(doorUnlocked.function(state, bTrue.union(bFalse)));

        // Event is also functional.
        // TODO very easy to forget this (I did) and then get told "Error: Root-cause extraction step returned SAT for transition; expected unsat."
        subs.add(next_door.function(state, bTrue.union(bFalse)));
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
        result.add(doorOpen); result.add(doorUnlocked);
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
            return "Door Open: " + sol.instance().relationTuples().get(doorOpen)+
                    " Unlocked: "+sol.instance().relationTuples().get(doorUnlocked)+
                    " Unlocked meaning flipped?: "+flipSignOfUnlocked;
        } else {
            return "UNSAT";
        }
    }

    @Override
    public void setBounds(Bounds bounds, Collection<Tuple> stateExactly) {
        TupleFactory factory = bounds.universe().factory();

        List<Tuple> next_doorUpper = new ArrayList<>();
        List<Tuple> doorUpper = new ArrayList<>();
        List<Tuple> lockedUpper = new ArrayList<>();

        for(Tuple st: stateExactly) {
            next_doorUpper.add(st.product(factory.tuple("TRUE")));
            next_doorUpper.add(st.product(factory.tuple("FALSE")));
            doorUpper.add(st.product(factory.tuple("TRUE")));
            doorUpper.add(st.product(factory.tuple("FALSE")));
            lockedUpper.add(st.product(factory.tuple("TRUE")));
            lockedUpper.add(st.product(factory.tuple("FALSE")));

        }

        bounds.bound(doorUnlocked, factory.setOf(lockedUpper));
        bounds.bound(doorOpen, factory.setOf(doorUpper));
        bounds.bound(next_door, factory.setOf(next_doorUpper));
        bounds.boundExactly(bTrue, factory.setOf(factory.tuple("TRUE")));
        bounds.boundExactly(bFalse, factory.setOf(factory.tuple("FALSE")));
    }

    @Override
    public String desc() {
        return "door open? door locked? once closed+locked can't be opened or unlocked. X property. infer unlock to start. flipped unlocked meaning: "+flipSignOfUnlocked;
    }
}

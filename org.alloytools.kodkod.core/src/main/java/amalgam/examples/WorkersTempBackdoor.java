package amalgam.examples;

import amalgam.cegis.Problem;
import kodkod.ast.*;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;

import java.util.*;

/*
  Same as the original, but with added level of indirection. Workers leave if they get uncomfortable.
 */
public class WorkersTempBackdoor implements Problem {
    private int backdoorTemperature = 75;
    private int minAComfy = 72;
    private int maxAComfy = 75;
    private int minBComfy = 50;
    private int maxBComfy = 100;

    private int minInt;
    private int maxInt;

    public WorkersTempBackdoor(int minInt, int maxInt) {
        this.minInt = minInt;
        this.maxInt = maxInt;
    }

    // Problem-specification relations (there are 2 people, they have comfort ranges)
    // These don't change over time, and they aren't something we synthesize. Take them as input.
    private static Relation comfyAt = Relation.binary("comfyAt");
    private static Relation personA = Relation.unary("PersonA");
    private static Relation personB = Relation.unary("PersonB");

    // Non-deployable configuration. These may be changed by the transition relation, but aren't
    // part of what we synthesize. We may have to take assumptions about these in order to synthesize correctly.
    // (For instance, assume the initial temperature setting isn't something uncomfy.)
    private static Relation setting = Relation.binary("setting");
    private static Relation occupants = Relation.binary("occupants");

    // Event relations. Must contain "EVENT_"
    private static Relation next_p = Relation.binary("EVENT_next_p");
    private static Relation next_target = Relation.binary("EVENT_next_target");

    // Deployable configuration: we have power over the *initial* value of these
    // Thus, synth phase uses a unary relation, and CE phase uses a binary relation.
    // IMPORTANT: we do some string comparison below; make sure config relations have CONF_ in them, and
    //   event relations have EVENT_ in them.
    private static Relation canSet = Relation.binary("DCONF_canSet");
    private static Relation allowedTemp = Relation.binary("DCONF_allowedTemp");

    @Override
    public Set<Formula> goals(Relation stateDomain, Expression enext, Expression lastState) {
        Variable p = Variable.unary("p");
        Variable s = Variable.unary("s");
        Formula Gboth = p.in(s.join(occupants)).forAll(s.oneOf(stateDomain)).forAll(p.oneOf(personA.union(personB)));
        return Collections.singleton(Gboth); // immutable
    }

    @Override
    public Set<Formula> additionalInitialConstraintsP1P2(Expression first) {
        Set<Formula> result = new HashSet<>();
        // Start out with a config that isn't empty...
        result.add(first.join(canSet).join(comfyAt).intersection(first.join(allowedTemp)).some());
        Variable p = Variable.unary("p");
        // Using forall, anticipating more people eventually
        result.add(p.join(comfyAt).intersection(first.join(allowedTemp)).count().gt(IntConstant.constant(1)).forAll(p.oneOf(personA.union(personB))));

        // Setting will start out comfortable.
        result.add(first.join(setting).in(p.join(comfyAt)).forAll(p.oneOf(personA.union(personB))));
        // Both people start out in the room
        result.add(personA.in(first.join(occupants)));
        result.add(personB.in(first.join(occupants)));

        return result;
    }

    /**
     * Construct the transition predicate for s --> s2.
     *
     * @param s The pre-state expression
     * @param s2 The post-state expression (often s.next, but engine controls "next").
     * @return
     */
    @Override
    public Formula buildTransition(Expression s, Expression s2) {
        Expression pretemp = s.join(setting);
        Expression preCanSet = s.join(canSet);
        Expression preAllowedTemp = s.join(allowedTemp);
        Expression posttemp = s2.join(setting);
        Expression postCanSet = s2.join(canSet);
        Expression postAllowedTemp = s2.join(allowedTemp);
        Expression p = s.join(next_p);
        Expression targ = s.join(next_target);
        Expression preOccupants = s.join(occupants);
        Expression postOccupants = s2.join(occupants);

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

        // For each person, they leave (and don't return) if uncomfy
        // Exercise IFF
        ante = pretemp.in(p.join(comfyAt));
        thenf = ante.implies(p.in(postOccupants).iff(p.in(preOccupants)));
        elsef = ante.not().implies(p.in(postOccupants).not());
        Formula locationChange = thenf.and(elsef);

        Formula transition = settingChange.and(policyChange).and(locationChange);
        return transition;
    }

    @Override
    public Set<Formula> structuralAxioms(Expression state) {
        Set<Formula> subs = new HashSet<>();
        subs.add(setting.function(state, Expression.INTS));
        subs.add(next_p.function(state, personA.union(personB)));
        subs.add(next_target.function(state, Expression.INTS));
        return subs;
    }

    @Override
    public Set<Relation> helperRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(comfyAt);
        return result;
    }

    @Override
    public Set<Relation> deployableRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(canSet); result.add(allowedTemp);
        return result;
    }

    @Override
    public Set<Relation> nondeployableRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(setting);
        result.add(occupants);
        return result;
    }

    @Override
    public Set<Relation> eventRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(next_p); result.add(next_target);
        return result;
    }

    @Override
    public Set<Relation> constantSingletonRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(personA);
        result.add(personB);
        return result;
    }

    @Override
    public String prettyConfigFromSynth(Solution sol) {
        if(sol.sat()) {
            return "Allowed Temps: " + sol.instance().relationTuples().get(allowedTemp) + " " +
                    "Can Set: " + sol.instance().relationTuples().get(canSet);
        } else {
            return "UNSAT";
        }
    }

    /**
     * For now, the problem has control over what gets provided as bounds and what gets provided as constraints.
     *
     * @param bounds The Bounds object to provide bounds to
     * @param stateExactly Assume this is the set of state atoms that the engine will use.
     *                     This is a parameter because different phases use different numbers of state atoms.
     *                     E.g., synthesis needs only 1, root-cause needs 2, etc.
     */
    @Override
    public void setBounds(Bounds bounds, Collection<Tuple> stateExactly) {
        TupleFactory factory = bounds.universe().factory();

        List<Tuple> comfyAts = new ArrayList<>();
        List<Tuple> settingUpper = new ArrayList<>();
        List<Tuple> next_pUpper = new ArrayList<>();
        List<Tuple> next_targetUpper = new ArrayList<>();
        List<Tuple> canSetUpper = new ArrayList<>();
        List<Tuple> allowedTempUpper = new ArrayList<>();
        List<Tuple> occupantsUpper = new ArrayList<>();

        for(int i=minAComfy; i<=maxAComfy; i++) {
            comfyAts.add(factory.tuple("PersonA", i));
        }
        for(int i=minBComfy; i<=maxBComfy; i++) {
            comfyAts.add(factory.tuple("PersonB", i));
        }

        for(Tuple st: stateExactly) {
            next_pUpper.add(st.product(factory.tuple("PersonA")));
            next_pUpper.add(st.product(factory.tuple("PersonB")));

            for(int j=minInt;j<=maxInt;j++) {
                next_targetUpper.add(st.product(factory.tuple(j)));
                settingUpper.add(st.product(factory.tuple(j)));
                allowedTempUpper.add(st.product(factory.tuple(j)));
            }

            // Don't include synthesized initial config in bounds (see below)

            canSetUpper.add(st.product(factory.tuple("PersonA")));
            canSetUpper.add(st.product(factory.tuple("PersonB")));

            occupantsUpper.add(st.product(factory.tuple("PersonA")));
            occupantsUpper.add(st.product(factory.tuple("PersonB")));
        }

        // We could bound the *FIRST* state's configuration here
        // However, since we want to use cores to extract blame in the initial config, we need to assert the
        // last-synthesized initial config as a formula. :-(
        // (Later states can be anything, hence non-exact bound)
        bounds.bound(canSet, factory.setOf(canSetUpper));
        bounds.bound(allowedTemp, factory.setOf(allowedTempUpper));
        bounds.bound(setting, factory.setOf(settingUpper));
        bounds.bound(occupants, factory.setOf(occupantsUpper));
        bounds.bound(next_p, factory.setOf(next_pUpper));
        bounds.bound(next_target, factory.setOf(next_targetUpper));
        bounds.boundExactly(comfyAt, factory.setOf(comfyAts));
        bounds.boundExactly(personA, factory.setOf(factory.tuple("PersonA")));
        bounds.boundExactly(personB, factory.setOf(factory.tuple("PersonB")));
    }

    @Override
    public String desc() {
        return "canSet/allowed with backdoor and workers who leave";
    }
}

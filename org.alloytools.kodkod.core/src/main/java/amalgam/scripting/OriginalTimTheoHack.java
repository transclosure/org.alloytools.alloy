package amalgam.scripting;

// TODO CEGIS will need a validator to check, e.g., that eventRelations all contain "EVENT_", that arities match, etc.

import kodkod.ast.*;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;

import java.util.*;

public class OriginalTimTheoHack implements SynthProblem {
    private int backdoorTemperature = 75;
    private int minAComfy = 72;
    private int maxAComfy = 75;
    private int minBComfy = 50;
    private int maxBComfy = 100;

    private int minInt;
    private int maxInt;

    OriginalTimTheoHack(int minInt, int maxInt) {
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

    @Override
    public Set<Formula> goals(Expression state) {
        Variable p = Variable.unary("p");
        Variable s = Variable.unary("s");
        Formula Gcomfy = s.join(setting).in(p.join(comfyAt)).forAll(p.oneOf(personA.union(personB))).forAll(s.oneOf(state));
        return Collections.singleton(Gcomfy); // immutable
    }

    @Override
    public Set<Formula> additionalConfigConstraints() {
        Set<Formula> result = new HashSet<>();
        // Start out with a config that isn't empty...
        result.add(canSetS.join(comfyAt).intersection(allowedTempS).some());
        Variable p = Variable.unary("p");
        // Using forall, anticipating more people eventually
        result.add(p.join(comfyAt).intersection(allowedTempS).count().gt(IntConstant.constant(1)).forAll(p.oneOf(personA.union(personB))));
        return result;
    }

    /**
     * Construct the transition predicate for s --> s2.
     * @param s The pre-state expression
     * @param s2 The post-state expression (often s.next, but engine controls "next").
     * @return
     */
    @Override
    public Formula buildTransition(Expression s, Expression s2) {
        Expression pretemp = s.join(setting);
        Expression preCanSet = s.join(canSetCE);
        Expression preAllowedTemp = s.join(allowedTempCE);
        Expression posttemp = s2.join(setting);
        Expression postCanSet = s2.join(canSetCE);
        Expression postAllowedTemp = s2.join(allowedTempCE);
        Expression p = s.join(next_p);
        Expression targ = s.join(next_target);

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

    @Override
    public Set<Formula> initialStateAssumptions(Expression first) {
        Set<Formula> subs = new HashSet<>();
        Variable p = Variable.unary("p");
        subs.add(first.join(setting).in(p.join(comfyAt)).forAll(p.oneOf(personA.union(personB))));
        return subs;
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
    public Set<Relation> deployableRelationsCE() {
        Set<Relation> result = new HashSet<>();
        result.add(canSetCE); result.add(allowedTempCE);
        return result;
    }

    @Override
    public Set<Relation> nondeployableRelationsCE() {
        Set<Relation> result = new HashSet<>();
        result.add(setting);
        return result;
    }

    @Override
    public Set<Relation> allStateRelationsCE() {
        Set<Relation> result = new HashSet<>(this.deployableRelationsCE());
        result.addAll(this.nondeployableRelationsCE());
        return result;
    }

    @Override
    public Set<Relation> eventRelationsCE() {
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
    public Relation ceToS(Relation ce) {
        if(canSetCE.equals(ce)) return canSetS;
        if(allowedTempCE.equals(ce)) return allowedTempS;
        throw new NoSuchElementException("ceToS: "+ce);
    }

    @Override
    public String prettyConfigFromSynth(Solution sol) {
        if(sol.sat()) {
            return "Allowed Temps: " + sol.instance().relationTuples().get(allowedTempS) + " " +
                    "Can Set: " + sol.instance().relationTuples().get(canSetS);
        } else {
            return "UNSAT";
        }
    }

    @Override
    public void setSynthBounds(Bounds bounds) {
        TupleFactory factory = bounds.universe().factory();

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
        bounds.boundExactly(comfyAt, factory.setOf(comfyAts));
        bounds.bound(canSetS, factory.setOf(canSetUpper));
        bounds.bound(allowedTempS, factory.setOf(allowedUpper));
        bounds.boundExactly(personA, factory.setOf(factory.tuple("PersonA")));
        bounds.boundExactly(personB, factory.setOf(factory.tuple("PersonB")));
    }

    @Override
    public void setCEBounds(Bounds bounds, Collection<Tuple> stateExactly) {
        TupleFactory factory = bounds.universe().factory();

        List<Tuple> settingUpper = new ArrayList<>();
        List<Tuple> next_pUpper = new ArrayList<>();
        List<Tuple> next_targetUpper = new ArrayList<>();
        List<Tuple> canSetUpper = new ArrayList<>();
        List<Tuple> allowedTempUpper = new ArrayList<>();

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
        }

        // We could bound the *FIRST* state's configuration here
        // However, since we want to use cores to extract blame in the initial config, we need to assert the
        // last-synthesized initial config as a formula. :-(
        // (Later states can be anything, hence non-exact bound)
        bounds.bound(canSetCE, factory.setOf(canSetUpper));
        bounds.bound(allowedTempCE, factory.setOf(allowedTempUpper));
        bounds.bound(setting, factory.setOf(settingUpper));
        bounds.bound(next_p, factory.setOf(next_pUpper));
        bounds.bound(next_target, factory.setOf(next_targetUpper));
    }
}

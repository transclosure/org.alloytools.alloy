package amalgam.scripting;

import kodkod.ast.*;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;

import java.util.*;

/**
 * Given N cities, partitioned into "good" and "bad" subsets, synthesize:
 *   (1) some one-way roads to build; and
 *   (2) a starting city
 * such that
 *   every good city is visited infinitely often; and
 *   every bad city is never visited
 * vs. the system that non-deterministically follows available roads.
 *
 * Note that most of the configuration here is monolithic: roads don't change.
 * However, (a) this is meant as a starting point to build examples from and (b)
 * even with unchanging roads, this can stress our system in interesting ways:
 * a liveness property, potentially non-trivial trace length, etc.
 * */

public class RoadsAndRoutes implements SynthProblem {

    int numCities;
    int numGood;
    int numBad;

    RoadsAndRoutes(int numGood, int numBad) {
        this.numCities = numGood + numBad;
        this.numGood = numGood;
        this.numBad = numBad;
    }


    // Event relations. Must contain "EVENT_"
    private static Relation next_city = Relation.binary("EVENT_next_city");

    // Helper: set of cities. Synthesis can't control these at all; they're given as part of the problem.
    private static Relation city = Relation.unary("City");
    private static Relation good = Relation.unary("GoodCity");
    private static Relation bad = Relation.unary("BadCity");

    // Deployable configuration: we have power over the *initial* value of these
    private static Relation roads = Relation.binary("DCONF_roads");
    private static Relation location = Relation.binary("DCONF_location");

    @Override
    public Set<Formula> goals(Relation stateDomain, Expression enext) {
        Variable s1 = Variable.unary("s1");
        Variable s2 = Variable.unary("s2");
        Variable gc = Variable.unary("gc"); // "good city"
        Variable bc = Variable.unary("bc"); // "bad city"
        // Good cities visited infinitely often (using quantification over good cities, too)
        Formula prop1 = s2.join(location).eq(gc)
                .forSome(s2.oneOf(s1.join(enext.reflexiveClosure())))
                .forAll(s1.oneOf(stateDomain))
                .forAll(gc.oneOf(good));
        // Bad cities never visited
        Formula prop2 = s1.join(location).eq(bc).not()
                .forAll(s1.oneOf(stateDomain));
        return Collections.singleton(prop1.and(prop2)); // immutable
    }

    @Override
    public Set<Formula> additionalInitialConstraintsP1P2(Expression first) {
        Set<Formula> result = new HashSet<>();
        return result;
    }

    @Override
    public Formula buildTransition(Expression s, Expression s2) {

        Formula validMove = s.join(next_city).in(s.join(location).join(roads));
        Formula transition1 = validMove.implies(s2.join(location).eq(s.join(next_city)));
        Formula transition2 = validMove.not().implies(s2.join(location).eq(s.join(location)));
        Formula roadsConstant = s2.join(roads).eq(s.join(roads));
        return transition1.and(transition2).and(roadsConstant);
    }

    @Override
    public Set<Formula> structuralAxioms(Expression state) {
        Set<Formula> subs = new HashSet<>();
        subs.add(location.function(state, city));
        // No constraints on roads (could be empty graph, could be complete)

        // Event is also functional.
        subs.add(next_city.function(state, city));
        return subs;
    }

    @Override
    public Set<Relation> helperRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(city); result.add(good); result.add(bad);
        return result;
    }

    @Override
    public Set<Relation> deployableRelations() {
        Set<Relation> result = new HashSet<>();
        result.add(location); result.add(roads);
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
        result.add(next_city);
        return result;
    }

    @Override
    public Set<Relation> constantSingletonRelations() {
        Set<Relation> result = new HashSet<>();
        return result;
    }

    @Override
    public String prettyConfigFromSynth(Solution sol) {
        if(sol.sat()) {
            return "Location:  " + sol.instance().relationTuples().get(location)+
                    " Roads: "+sol.instance().relationTuples().get(roads);
        } else {
            return "UNSAT";
        }
    }

    @Override
    public void setBounds(Bounds bounds, Collection<Tuple> stateExactly) {
        TupleFactory factory = bounds.universe().factory();

        List<Tuple> cityExact = new ArrayList<>();
        List<Tuple> goodExact = new ArrayList<>();
        List<Tuple> badExact = new ArrayList<>();
        List<Tuple> next_cityUpper = new ArrayList<>();
        List<Tuple> locUpper = new ArrayList<>();

        for(int i = 0; i<numGood; i++) {
            goodExact.add(factory.tuple("Good"+i));
            cityExact.add(factory.tuple("Good"+i));
        }
        for(int i = 0; i<numBad; i++) {
            badExact.add(factory.tuple("Bad"+i));
            cityExact.add(factory.tuple("Bad"+i));
        }

        TupleSet stateSet = factory.noneOf(1);
        for(Tuple st: stateExactly) {
            for(int i = 0; i<numGood; i++) {
                next_cityUpper.add(st.product(factory.tuple("Good"+i)));
                locUpper.add(st.product(factory.tuple("Good"+i)));
            }
            for(int i = 0; i<numBad; i++) {
                next_cityUpper.add(st.product(factory.tuple("Bad" + i)));
                locUpper.add(st.product(factory.tuple("Bad" + i)));
            }
            stateSet.add(st);
        }

        bounds.boundExactly(city, factory.setOf(cityExact));
        bounds.boundExactly(good, factory.setOf(goodExact));
        bounds.boundExactly(bad, factory.setOf(badExact));
        bounds.bound(next_city, factory.setOf(next_cityUpper));
        bounds.bound(location, factory.setOf(locUpper));
        bounds.bound(roads, stateSet.product(bounds.upperBound(city)).product(bounds.upperBound(city)));
    }

    @Override
    public String desc() {
        return "build (static) roads and starting location, GF+G";
    }
}

package amalgam.examples;

import amalgam.cegis.Problem;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;

import java.util.*;

public class RoadsSafety implements Problem {
    int numCities;
    int numGood;
    int numBad;

    public RoadsSafety(int numGood, int numBad) {
        this.numCities = numGood + numBad;
        this.numGood = numGood;
        this.numBad = numBad;

        for(int i = 0; i<numGood; i++) {
            cities.add(Relation.unary("Good"+i));
        }
        for(int i = 0; i<numBad; i++) {
            cities.add(Relation.unary("Bad"+i));
        }
    }


    // Event relations. Must contain "EVENT_"
    private static Relation next_city = Relation.binary("EVENT_next_city");

    // Helper: set of cities. Synthesis can't control these at all; they're given as part of the problem.
    private static Relation city = Relation.unary("City");
    private static Relation good = Relation.unary("GoodCity");
    private static Relation bad = Relation.unary("BadCity");

    // Constants: individual names for the cities
    private static Set<Relation> cities = new HashSet<>();

    // Deployable configuration: we have power over the *initial* value of these
    private static Relation roads = Relation.nary("DCONF_roads", 3);
    private static Relation location = Relation.binary("DCONF_location");

    @Override
    public Set<Formula> goals(Relation stateDomain, Expression enext) {
        Variable s1 = Variable.unary("s1");
        Variable sj = Variable.unary("sj");
        Variable sw = Variable.unary("sw");
        Variable gc1 = Variable.unary("gc1"); // "good city 1"
        Variable gc2 = Variable.unary("gc2"); // "good city 2"
        Variable bc = Variable.unary("bc"); // "bad city"

        // Don't re-visit x until you've visited all the others.
        // Note: this is *weak until*. May not revisit x at all.
        // G(loc=x --> X(~(loc=x) W loc=y))
        // ...but see below re: absorbing stuttering
        // s1 = the outer G. sx = the state after s1.
        // sw = the forall induced by the W. sj = the bounded existential in scope of sw.
        Expression sx = s1.join(enext);

        // at this post-next-state state, ~(loc=x)
        Formula option1 = sw.join(location).eq(gc1).not();
        // OR sometime sj \in [sx, sw], visited y. Encode this by saying "after sx, before sw (inclusive).
        Expression afterSXIncl = sx.join(enext.reflexiveClosure());
        Expression beforeSWIncl = sw.join(enext.transpose().reflexiveClosure());
        Formula option2 = sj.join(location).eq(gc2).forSome(sj.oneOf(afterSXIncl.intersection(beforeSWIncl)));
        Formula consequent = option1.or(option2).forAll(sw.oneOf(sx.join(enext.closure()))); // for every state after sx
        // Absorb stuttering in case of "denied" event: loc=x /\ X(loc!=x), not just loc=x.
        Formula prop1 = s1.join(location).eq(gc1).and(sx.join(location).eq(gc1).not()).implies(consequent)
                .forAll(s1.oneOf(stateDomain))
                .forAll(gc2.oneOf(good.difference(gc1))).forAll(gc1.oneOf(good));


        // Bad cities never visited
        Formula prop2 = s1.join(location).eq(bc).not()
                .forAll(s1.oneOf(stateDomain))
                .forAll(bc.oneOf(bad));
        Set<Formula> result = new HashSet<>();
        result.add(prop1);
        result.add(prop2);
        return result;
    }

    @Override
    public Set<Formula> additionalInitialConstraintsP1P2(Expression first) {
        Set<Formula> result = new HashSet<>();

        // Require strongly connected (good) cities
        Variable c1 = Variable.unary("c1");
        Variable c2 = Variable.unary("c2");
        Formula reachable = c1.eq(c2).not().implies(c1.in(c2.join(first.join(roads).closure())));
        reachable = reachable.forAll(c2.oneOf(good)).forAll(c1.oneOf(good));
        result.add(reachable);

        // No self-loops for any city (avoid noise in output)
        Formula antireflexive = c1.in(c1.join(first.join(roads))).not().forAll(c1.oneOf(city));
        result.add(antireflexive);
        return result;
    }

    @Override
    public Formula buildTransition(Expression s, Expression s2) {
        // Need explicit event to break non-determinism in blame.
        Formula validMove = s.join(next_city).in(s.join(location).join(s.join(roads)));
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
        return cities;
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

        for(Relation r : cities) {
            bounds.boundExactly(r, factory.setOf(factory.tuple(r.name())));
        }

        bounds.boundExactly(city, factory.setOf(cityExact));
        bounds.boundExactly(good, factory.setOf(goodExact));
        if(numBad < 1)
            bounds.boundExactly(bad, factory.noneOf(1));
        else
            bounds.boundExactly(bad, factory.setOf(badExact));
        bounds.bound(next_city, factory.setOf(next_cityUpper));
        bounds.bound(location, factory.setOf(locUpper));
        bounds.bound(roads, stateSet.product(bounds.upperBound(city)).product(bounds.upperBound(city)));
    }

    @Override
    public String desc() {
        return "build (static) roads and starting location, G+GW. Safety only, plus axiom.";
    }

}

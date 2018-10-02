package amalgam.examples;

import kodkod.ast.*;
import kodkod.ast.SubstituteVisitor;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.instance.*;

import java.util.*;

public class HomeNet implements KodkodExample {

    // Kodkod
    private final Relation device, interfac;
    private final Relation connected;
    public HomeNet() {
        device = Relation.unary("Device");
        interfac = Relation.unary("Interface");
        connected = Relation.binary("connected");
    }
    @Override
    public Bounds bounds(int n) {
        // Universe
        List<String> atoms = new ArrayList<>();
        for(int i=1; i<=n; i++) {
            atoms.add("Device"+i);
            atoms.add("Interface"+i);
        }
        final Universe universe = new Universe(atoms);
        final TupleFactory factory = universe.factory();
        // Relations
        List<Tuple> devices = new ArrayList<>();
        List<Tuple> interfacs = new ArrayList<>();
        List<Tuple> connecteds = new ArrayList<>();
        for(int i=1; i<=n; i++) {
            devices.add(factory.tuple("Device"+i));
            interfacs.add(factory.tuple("Interface"+i));
            for(int j=1; j<=n; j++) {
                connecteds.add(factory.tuple("Device"+i, "Interface"+j));
            }
        }
        // Bounds
        Bounds bounds = new Bounds(universe);
        bounds.bound(device, factory.setOf(devices));
        bounds.bound(interfac, factory.setOf(interfacs));
        bounds.bound(connected, factory.setOf(connecteds));

        // Add constant symbols
        for(String a: atoms) {
            Relation ra = Relation.unary(a);
            bounds.boundExactly(ra, factory.setOf(factory.tuple(a)));
        }

        return bounds;
    }
    @Override
    public Formula verifyformula() {
        final List<Formula> formulas = new ArrayList<>();
        // force connected to be on (Device X Interface)
        final Formula leftComponentInDevice = connected.join(Expression.UNIV).in(device);
        final Formula rightComponentInInterface = Expression.UNIV.join(connected).in(interfac);
        formulas.add(leftComponentInDevice);
        formulas.add(rightComponentInInterface);
        // total
        final Variable i1 = Variable.unary("i");
        final Variable d1 = Variable.unary("d");
        final Formula total = d1.join(connected).compare(ExprCompOperator.EQUALS, i1);
        formulas.add(total.forSome(i1.oneOf(interfac)).forAll(d1.oneOf(device)));
        // one-to-one
        final Variable dA = Variable.unary("dA");
        final Variable dB = Variable.unary("dB");
        final Formula lhs1 = dA.compare(ExprCompOperator.EQUALS, dB).not();
        final Formula rhs1 = dA.join(connected).compare(ExprCompOperator.EQUALS, dB.join(connected)).not();
        formulas.add(lhs1.implies(rhs1).forAll(dB.oneOf(device)).forAll(dA.oneOf(device)));
        // needle in haystack
        formulas.add(connected.count().eq(IntConstant.constant(7)));
        //
        return Formula.and(formulas);
    }

    // CEGIS
    @Override
    public Formula synthformula() {
        final List<Formula> formulas = new ArrayList<>();
        // force connected to be on (Device X Interface)
        final Formula leftComponentInDevice = connected.join(Expression.UNIV).in(device);
        final Formula rightComponentInInterface = Expression.UNIV.join(connected).in(interfac);
        formulas.add(leftComponentInDevice);
        formulas.add(rightComponentInInterface);
        // non-trivial
        formulas.add(connected.some());
        //
        return Formula.and(formulas);
    }

    // TN note: there is some code duplication here; I didn't want to clobber existing code in a quick test hack
    @Override
    public Collection<KodkodExample.SynthGoal> goals() {
        final List<KodkodExample.SynthGoal> results = new ArrayList<>();
        final List<Formula> formulas = new ArrayList<>();
        final Map<Variable, Expression> univars = new HashMap<>();

        // total
        final Variable i1 = Variable.unary("i");
        final Variable d1 = Variable.unary("d");
        univars.put(d1, device); // i1 is existential
        final Formula total = d1.join(connected).one();
        //formulas.add(total.forSome(i1.oneOf(interfac)).forAll(d1.oneOf(device)));
        formulas.add(total);
        results.add(new HomeNetGoal(univars, Formula.and(formulas)));
        formulas.clear(); univars.clear();

        // one-to-one
        final Variable dA = Variable.unary("dA");
        final Variable dB = Variable.unary("dB");
        univars.put(dA, device); univars.put(dB, device);
        final Formula lhs1 = dA.compare(ExprCompOperator.EQUALS, dB).not();
        final Formula rhs1 = dA.join(connected).compare(ExprCompOperator.EQUALS, dB.join(connected)).not();
        //formulas.add(lhs1.implies(rhs1).forAll(dB.oneOf(device)).forAll(dA.oneOf(device)));
        formulas.add(lhs1.implies(rhs1));
        results.add(new HomeNetGoal(univars, Formula.and(formulas)));
        formulas.clear(); univars.clear();

        // needle in haystack
        formulas.add(connected.count().eq(IntConstant.constant(7)));
        results.add(new HomeNetGoal(univars, Formula.and(formulas)));
        formulas.clear(); univars.clear();

        return results;
    }

    @Override
    public Bounds restrict(Bounds verifybounds, Instance synth, boolean onlySkeleton) {
        Bounds restricted = verifybounds.clone();
        restricted.boundExactly(device, synth.tuples(device));
        if(!onlySkeleton) {
            restricted.boundExactly(interfac, synth.tuples(interfac));
            restricted.boundExactly(connected, synth.tuples(connected));
        }
        return restricted;
    }
    @Override
    public Bounds refine(Bounds synthbounds, Instance synth, Instance verify)  {
        Bounds refined = synthbounds.clone();
        /* Exclude previous synth attempt, naive
        Map<Relation,TupleSet> exclude = new LinkedHashMap<>();
        exclude.put(synthbounds.findRelByName("Device"), synth.tuples("Device"));
        exclude.put(synthbounds.findRelByName("Interface"), synth.tuples("Interface"));
        exclude.put(synthbounds.findRelByName("connected"), synth.tuples("connected"));
        refined.exclude(exclude);
        */
        if(verify ==null) {
            // Exclude synth skeleton
            Map<Relation,TupleSet> exclude = new LinkedHashMap<>();
            exclude.put(device, synth.tuples(device));
            refined.exclude(exclude);
            // gravitate away from skeleton
            Map<Relation,TupleSet> target = new LinkedHashMap<>();
            TupleSet deviceM = synth.tuples(device);
            List<Tuple> deviceN = new ArrayList<>();
            int n = synthbounds.upperBound(device).size();
            for(int i=1; i<=n; i++) {
                Tuple tuple = synthbounds.universe().factory().tuple("Device" + i);
                if(!deviceM.contains(tuple)) deviceN.add(tuple);
            }
            if(!deviceN.isEmpty()) {
                target.put(device, synthbounds.universe().factory().setOf(deviceN));
                refined.target(target);
            }
        } else {
            // Include verify witness
            Map<Relation,TupleSet> include = new LinkedHashMap<>();
            include.put(connected, verify.tuples(connected));
            refined.include(include);
        }
        return refined;
    }

    // Target-oriented
    @Override
    public Bounds target(Bounds bounds) { return bounds; }
}

class HomeNetGoal implements KodkodExample.SynthGoal {
    Map<Variable, Expression> freevars;
    Formula unboundformula;
    Formula boundformula;

    HomeNetGoal(Map<Variable, Expression> freevars, Formula unboundformula) {
        this.freevars = new HashMap(freevars);
        this.unboundformula = unboundformula;
        this.boundformula = unboundformula;
        for(Variable v : freevars.keySet()) {
            this.boundformula = this.boundformula().forAll(v.oneOf(freevars.get(v)));
        }
    }
    public Map<Variable, Expression> freevars() { return freevars; }
    public Formula unboundformula() { return unboundformula; }
    public Formula boundformula() { return boundformula; }

    public Formula instantiateWithCE(Instance ce, Bounds b) {
        // Need to produce phi(ce).
        Formula f = unboundformula;
        System.out.println("instantiateWithCE: "+freevars);
        for(Variable v : freevars.keySet()) {
            Relation skolemRel = ce.findRelationByName("$"+v);
            TupleSet relTuples = ce.relationTuples().get(skolemRel);
            String constStr = "";
            // TODO: hack! assume that the name of the relation and the name of the atom are the same Java string
            for(Tuple t : relTuples) {
                constStr = t.atom(0).toString();
                break;
            }
            f = f.accept(new SubstituteVisitor(v, b.findRelByName(constStr)));
        }
        return f;
    }

}
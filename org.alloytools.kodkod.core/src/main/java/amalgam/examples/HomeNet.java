package amalgam.examples;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.instance.*;

import java.text.Normalizer;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class HomeNet implements KodkodExample {

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
        final Bounds bounds = new Bounds(universe);
        bounds.bound(device, factory.setOf(devices));
        bounds.bound(interfac, factory.setOf(interfacs));
        bounds.bound(connected, factory.setOf(connecteds));
        return bounds;
    }

    @Override
    public Formula refine(Formula current, Instance refinement)  {
        // TODO and with negate diagram of refinement instance
        return current;
    }

    @Override
    public Bounds restrict(Bounds current, Instance restriction) {
        Bounds restricted = current.clone();
        restricted.boundExactly(connected, restriction.tuples("connected"));
        return restricted;
    }

    @Override
    public Formula formula() {
        final List<Formula> formulas = new ArrayList<>();
        // total
        final Variable i = Variable.unary("i");
        final Variable d = Variable.unary("d");
        Formula total = d.join(connected).compare(ExprCompOperator.EQUALS, i);
        formulas.add(total.forSome(i.oneOf(interfac)).forAll(d.oneOf(device)));
        // one-to-one
        final Variable dA = Variable.unary("dA");
        final Variable dB = Variable.unary("dB");
        Formula lhs = dA.compare(ExprCompOperator.EQUALS, dB).not();
        Formula rhs = dA.join(connected).compare(ExprCompOperator.EQUALS, dB.join(connected)).not();
        formulas.add(lhs.implies(rhs).forAll(dB.oneOf(device)).forAll(dA.oneOf(device)));
        // non-trivial
        formulas.add(connected.some());
        //
        return Formula.and(formulas);
    }

    @Override
    public Map<Relation,TupleSet> target(Bounds bounds) { return null; }
}

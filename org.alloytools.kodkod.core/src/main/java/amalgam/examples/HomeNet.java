package amalgam.examples;

import kodkod.ast.*;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.ExprOperator;
import kodkod.instance.*;

import java.text.Normalizer;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Stream;

public class HomeNet implements KodkodExample {

    private final Relation device, interfac;
    private final Relation connected;
    private Bounds bounds;

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
        bounds = new Bounds(universe);
        bounds.bound(device, factory.setOf(devices));
        bounds.bound(interfac, factory.setOf(interfacs));
        bounds.bound(connected, factory.setOf(connecteds));
        return bounds;
    }

    @Override
    public Formula refine(Formula current, Instance refinement)  { return current; }

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
        // non-trivial
        formulas.add(connected.count().gt(IntConstant.constant(3)));
        //
        return Formula.and(formulas);
    }

    @Override
    public Map<Relation,TupleSet> target(Bounds bounds) { return null; }
}

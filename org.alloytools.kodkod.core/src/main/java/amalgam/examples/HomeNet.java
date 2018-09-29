package amalgam.examples;

import com.sun.xml.internal.ws.api.message.Packet;
import kodkod.ast.*;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.instance.*;

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
        Bounds bounds = new Bounds(universe);
        bounds.bound(device, factory.setOf(devices));
        bounds.bound(interfac, factory.setOf(interfacs));
        bounds.bound(connected, factory.setOf(connecteds));
        return bounds;
    }

    @Override
    public Bounds refine(Bounds synthbounds, Instance avoid)  {
        Bounds refined = synthbounds.clone();
        // not-model as a target oriented bound (get a maxsat point for each tuple avoided)
        // z3 solver side effect handles how targets become clauses
        // things like priority, composition of targets, etc, are dealt with there
        Map<Relation,List<Tuple>> targets = new LinkedHashMap<>();
        TupleSet connectedM = avoid.tuples("connected");
        List<Tuple> connectedN = new ArrayList<>();
        int n = synthbounds.upperBound(device).size();
        for(int i=1; i<=n; i++) {
            for (int j = 1; j<=n; j++) {
                Tuple tuple = synthbounds.universe().factory().tuple("Device" + i, "Interface" + j);
                if(!connectedM.contains(tuple)) {
                    connectedN.add(tuple);
                }
            }
        }
        targets.put(synthbounds.findRelByName("connected"), connectedN);
        refined.addTarget(targets);
        return refined;
    }

    @Override
    public Bounds restrict(Bounds verifybounds, Instance apply) {
        Bounds restricted = verifybounds.clone();
        restricted.boundExactly(connected, apply.tuples("connected"));
        return restricted;
    }

    @Override
    public Formula synthformula() {
        return connected.some();
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
        formulas.add(connected.count().eq(IntConstant.constant(7)));
        //
        return Formula.and(formulas);
    }

    @Override
    public Bounds target(Bounds bounds) { return bounds; }
}

package amalgam.examples;

import java.text.Normalizer;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.instance.*;

public final class DataRepair implements KodkodExample {

    private final Relation node, hue;
    private final Relation adj, color;

    public DataRepair() {
        node = Relation.unary("Node");
        hue = Relation.unary("Hue");
        adj = Relation.binary("adj");
        color = Relation.binary("color");
    }

    @Override
    public Bounds bounds(int n) {
        // Universe
        List<String> atoms = new ArrayList<>();
        for(int i=1; i<=n; i++) {
            atoms.add("Node"+i);
            atoms.add("Hue"+i);
        }
        final Universe universe = new Universe(atoms);
        final TupleFactory factory = universe.factory();
        // Relations
        List<Tuple> nodes = new ArrayList<>();
        List<Tuple> hues = new ArrayList<>();
        List<Tuple> adjs = new ArrayList<>();
        List<Tuple> colors = new ArrayList<>();
        for(int i=1; i<=n; i++) {
            nodes.add(factory.tuple("Node"+i));
            hues.add(factory.tuple("Hue"+i));
            adjs.add(i==n ? factory.tuple("Node"+i, "Node"+(i-1)) : factory.tuple("Node"+i, "Node"+(i+1)));
            for(int j=1; j<=n; j++) {
                colors.add(factory.tuple("Node"+i, "Hue"+j));
            }
        }
        // Bounds
        Bounds bounds = new Bounds(universe);
        bounds.boundExactly(node, factory.setOf(nodes));
        bounds.boundExactly(hue, factory.setOf(hues));
        bounds.boundExactly(adj, factory.setOf(adjs));
        bounds.bound(color, factory.setOf(colors));
        return bounds;
    }

    @Override
    public Formula refine(Formula current, Instance refinement)  {
        return current;
    }

    @Override
    public Bounds restrict(Bounds current, Instance restriction) { return current; }

    @Override
    public Formula formula() {
        final List<Formula> formulas = new ArrayList<>();
        final Variable n = Variable.unary("n");
        final Variable m = Variable.unary("m");
        // first constraint
        formulas.add(n.join(color).one().forAll(n.oneOf(node)));
        // second constraint
        Formula l = n.in(m.join(adj.reflexiveClosure())).and(m.in(n.join(adj.reflexiveClosure())));
        Formula r = n.join(color).eq(m.join(color));
        formulas.add(l.iff(r).forAll(n.oneOf(node).and(m.oneOf(node))));
        return Formula.and(formulas);
    }

    @Override
    public Map<Relation,TupleSet> target(Bounds bounds) {
        Map<Relation,TupleSet> targets = new LinkedHashMap<>();
        List<Tuple> colors = new ArrayList<>();
        int n = bounds.upperBound(node).size();
        for(int i=1; i<=n; i++) {
            colors.add(bounds.universe().factory().tuple("Node"+i, "Hue"+i));
        }
        targets.put(bounds.findRelByName("color"), bounds.universe().factory().setOf(colors));
        return targets;
    }
}

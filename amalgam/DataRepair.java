/*
 * Kodkod -- Copyright (c) 2005-2008, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

public final class DataRepair {

    public static void main(String[] args) {
        final DataRepair spec = new DataRepair();
        final Formula f = spec.constraints();
        final Bounds lowb = spec.bounds(20);
        final Bounds highb = spec.bounds(100);
        exec(f, lowb);
        exec(f, highb);
    }

    private static void exec(Formula f, Bounds b) {
        final Solver solver = new Solver();
        solver.options().setSolver(SATFactory.Z3);
        solver.options().setSymmetryBreaking(0);
        solver.options().setSkolemDepth(-1);
        solver.options().setLogTranslation(2);
        final Solution s = solver.solve(f, b);
        System.out.println(s);
    }

    private final Relation node, hue;
    private final Relation adj, color;

    private DataRepair() {
        node = Relation.unary("Node");
        hue = Relation.unary("Hue");
        adj = Relation.binary("adj");
        color = Relation.binary("color");
    }

    private final Bounds bounds(int n) {
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
        final Bounds bounds = new Bounds(universe);
        bounds.boundExactly(node, factory.setOf(nodes));
        bounds.boundExactly(hue, factory.setOf(hues));
        bounds.boundExactly(adj, factory.setOf(adjs));
        bounds.bound(color, factory.setOf(colors));
        return bounds;
    }

    private final Formula constraints() {
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
}

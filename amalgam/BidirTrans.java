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

import java.util.ArrayList;
import java.util.List;

public final class BidirTrans {

    public static void main(String[] args) {
        final BidirTrans spec = new BidirTrans();
        final Formula f = spec.constraints();
        final Bounds lowb = spec.bounds(8);
        final Bounds highb = spec.bounds(20);
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

    private final Relation thing, table, name;
    private final Relation namec, namet, attr, col, per, parent;

    private BidirTrans() {
        thing = Relation.unary("Class");
        table = Relation.unary("Table");
        name = Relation.unary("Name");
        namec = Relation.binary("namec");
        namet = Relation.binary("namet");
        attr = Relation.binary("attributes");
        col = Relation.binary("columns");
        per = Relation.unary("persistent");
        parent = Relation.binary("parent");
    }

    private final Bounds bounds(int n) {
        // Universe
        List<String> atoms = new ArrayList<>();
        for(int i=1; i<=n; i++) {
            atoms.add("Class"+i);
            atoms.add("Class"+(n+i));
            atoms.add("Name"+i);
            atoms.add("Name"+(n+i));
            atoms.add("Table"+i);
        }
        final Universe universe = new Universe(atoms);
        final TupleFactory factory = universe.factory();
        // Relations
        List<Tuple> things = new ArrayList<>();
        List<Tuple> tables = new ArrayList<>();
        List<Tuple> names = new ArrayList<>();
        List<Tuple> namecs = new ArrayList<>();
        List<Tuple> namets = new ArrayList<>();
        List<Tuple> attrs = new ArrayList<>();
        List<Tuple> cols = new ArrayList<>();
        List<Tuple> pers = new ArrayList<>();
        List<Tuple> parents = new ArrayList<>();
        for(int i=1; i<=n; i++) {
            things.add(factory.tuple("Class"+i));
            things.add(factory.tuple("Class"+(n+i)));
            names.add(factory.tuple("Name"+i));
            names.add(factory.tuple("Name"+(n+i)));
            tables.add(factory.tuple("Table"+i));
            namets.add(factory.tuple("Table"+i, "Name"+(n+i)));
            for(int j=1; j<=n; j++) {
                namecs.add(factory.tuple("Class"+i, "Name"+j));
                attrs.add(factory.tuple("Class"+i, "Name"+j));
                parents.add(factory.tuple("Class"+i, "Class"+j));
            }
            pers.add(factory.tuple("Class"+i));
            pers.add(factory.tuple("Class"+(n+i)));
        }
        // FIXME semantically unclear in paper
        for(int i=1; i<n; i++) {
            cols.add(factory.tuple("Table" + i, "Name" + i));
            cols.add(factory.tuple("Table" + (i + 1), "Name" + i));
            cols.add(factory.tuple("Table" + (i + 1), "Name" + (i + 1)));
        }
        // Bounds
        final Bounds bounds = new Bounds(universe);
        bounds.bound(thing, factory.setOf(things));
        bounds.boundExactly(table, factory.setOf(tables));
        bounds.bound(name, factory.setOf(names));
        bounds.bound(namec, factory.setOf(namecs));
        bounds.boundExactly(namet, factory.setOf(namets));
        bounds.bound(attr, factory.setOf(attrs));
        bounds.boundExactly(col, factory.setOf(cols));
        bounds.bound(per, factory.setOf(pers));
        bounds.bound(parent, factory.setOf(parents));
        return bounds;
    }

    private final Formula constraints() {
        final List<Formula> formulas = new ArrayList<>();
        final Variable c = Variable.unary("c");
        final Variable n = Variable.unary("n");
        final Variable t = Variable.unary("t");
        //
        formulas.add(per.in(thing));
        formulas.add(attr.in(thing.product(name)));
        formulas.add(namec.in(thing.product(name)));
        formulas.add(parent.in(thing.product(thing)));
        //
        formulas.add(c.join(namec).one().forAll(c.oneOf(thing)));
        formulas.add(namec.join(n).lone().forAll(n.oneOf(name)));
        formulas.add(c.join(parent).lone().forAll(c.oneOf(thing)));
        formulas.add(c.in(c.join(parent.closure())).not().forAll(c.oneOf(thing)));
        //
        Formula l = c.join(namec).eq(t.join(namet));
        Formula r = c.join(parent.reflexiveClosure()).join(attr).eq(t.join(col));
        formulas.add(l.and(r).forSome(t.oneOf(table)).forAll(c.oneOf(per)));
        formulas.add(l.and(r).forSome(c.oneOf(per)).forAll(t.oneOf(table)));
        //
        return Formula.and(formulas);
    }
}

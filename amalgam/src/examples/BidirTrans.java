package examples;/*
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
import kodkod.instance.*;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class BidirTrans implements KodkodExample {

    private final Relation thing, table, name;
    private final Relation namec, namet, attr, col, per, parent;

    public BidirTrans() {
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

    @Override
    public Bounds bounds(int n) {
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
                namecs.add(factory.tuple("Class"+i, "Name"+(n+j)));
                attrs.add(factory.tuple("Class"+i, "Name"+j));
                parents.add(factory.tuple("Class"+i, "Class"+j));
            }
            for(int j=1; j<=i; j++) {
                cols.add(factory.tuple("Table" + i, "Name" + j));
            }
            pers.add(factory.tuple("Class"+i));
            pers.add(factory.tuple("Class"+(n+i)));
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

    @Override
    public Formula formula() {
        final List<Formula> formulas = new ArrayList<>();
        //
        formulas.add(per.in(thing));
        formulas.add(attr.in(thing.product(name)));
        formulas.add(namec.in(thing.product(name)));
        formulas.add(parent.in(thing.product(thing)));
        //
        final Variable c = Variable.unary("c");
        final Variable n = Variable.unary("n");
        formulas.add(c.join(namec).one().forAll(c.oneOf(thing)));
        formulas.add(namec.join(n).lone().forAll(n.oneOf(name)));
        formulas.add(c.join(parent).lone().forAll(c.oneOf(thing)));
        formulas.add(c.in(c.join(parent.closure())).not().forAll(c.oneOf(thing)));
        //
        final Variable c1 = Variable.unary("c");
        final Variable t1 = Variable.unary("t");
        final Formula l1 = c1.join(namec).eq(t1.join(namet));
        final Formula r1 = c1.join(parent.reflexiveClosure()).join(attr).eq(t1.join(col));
        formulas.add(l1.and(r1).forSome(t1.oneOf(table)).forAll(c1.oneOf(per)));
        final Variable c2 = Variable.unary("c");
        final Variable t2 = Variable.unary("t");
        final Formula l2 = c2.join(namec).eq(t2.join(namet));
        final Formula r2 = c2.join(parent.reflexiveClosure()).join(attr).eq(t2.join(col));
        formulas.add(l2.and(r2).forSome(c2.oneOf(per)).forAll(t2.oneOf(table)));
        //
        return Formula.and(formulas);
    }

    @Override
    public Map<Relation,TupleSet> targets(Bounds bounds) {
        Map<Relation,TupleSet> targets = new LinkedHashMap<>();
        List<Tuple> things = new ArrayList<>();
        List<Tuple> names = new ArrayList<>();
        List<Tuple> namecs = new ArrayList<>();
        List<Tuple> attrs = new ArrayList<>();
        List<Tuple> pers = new ArrayList<>();
        List<Tuple> parents = new ArrayList<>();
        int n = bounds.upperBound(table).size();
        for(int i=1; i<=2*n; i++) {
            things.add(bounds.universe().factory().tuple("Class"+i));
            names.add(bounds.universe().factory().tuple("Name"+i));
            namecs.add(bounds.universe().factory().tuple("Class"+i, "Name"+i));
            attrs.add(bounds.universe().factory().tuple("Class"+i, "Name"+i));
        }
        for(int i=1; i<=n; i++) {
            pers.add(bounds.universe().factory().tuple("Class"+i));
        }
        for(int i=1; i<=2*n; i++) {
            for(int j=1; j<=2*n; j++) {
                if (i!=j) {
                    parents.add(bounds.universe().factory().tuple("Class" + i, "Class" + j));
                }
            }
        }
        targets.put(bounds.findRelByName("Class"), bounds.universe().factory().setOf(things));
        targets.put(bounds.findRelByName("Name"), bounds.universe().factory().setOf(names));
        targets.put(bounds.findRelByName("namec"), bounds.universe().factory().setOf(namecs));
        targets.put(bounds.findRelByName("attributes"), bounds.universe().factory().setOf(attrs));
        targets.put(bounds.findRelByName("persistent"), bounds.universe().factory().setOf(pers));
        targets.put(bounds.findRelByName("parent"), bounds.universe().factory().setOf(parents));
        return targets;
    }
}

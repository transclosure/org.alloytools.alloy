package amalgam.scripting;

import amalgam.examples.BidirTrans;
import amalgam.examples.DataRepair;
import amalgam.examples.KodkodExample;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

public class Evaluation {

    public static void main(String[] args) {
        KodkodExample spec;
        SATFactory solver;
        Bounds lowb;
        Bounds highb;

        spec = new DataRepair();
        solver = SATFactory.Z3;
        lowb = spec.bounds(20);
        highb = spec.bounds(100);
        time("datarepair 20 z3", spec.formula(), lowb, solver, 3);
        //time("datarepair 100 z3", spec.formula(), highb, solver, 1);
        lowb.boundTargets(spec.targets(lowb));
        highb.boundTargets(spec.targets(highb));
        time("datarepair 20 z3+target", spec.formula(), lowb, solver, 3);
        //time("datarepair 100 z3+target", spec.formula(), highb, solver, 1);

        spec = new BidirTrans();
        solver = SATFactory.Z3;
        lowb = spec.bounds(8);
        highb = spec.bounds(20);
        time("bidirtrans 8 z3", spec.formula(), lowb, solver, 3);
        time("bidirtrans 20 z3", spec.formula(), highb, solver, 3);
        lowb.boundTargets(spec.targets(lowb));
        highb.boundTargets(spec.targets(highb));
        time("bidirtrans 8 z3+target", spec.formula(), lowb, solver, 3);
        //time("bidirtrans 20 z3+target", spec.formula(), highb, solver, 1);
    }

    private static void time(String name, Formula f, Bounds b, SATFactory s, int outof) {
        System.out.println(name);
        System.out.println("--------------------");
        double transtotal = 0;
        double solvetotal = 0;
        for(int i=0; i<outof; i++) {
            Solution sol = exec(f, b, s);
            long trans = sol.stats().translationTime();
            long solve = sol.stats().solvingTime();
            System.out.println(trans + "\t"+ solve);
            transtotal += trans;
            solvetotal += solve;
        }
        System.out.println("--------------------");
        System.out.println(transtotal / outof + "\t"+ solvetotal / outof);
        System.out.println("");
    }
    private static Solution exec(Formula f, Bounds b, SATFactory s) {
        final Solver solver = new Solver();
        solver.options().setSolver(s);
        solver.options().setSymmetryBreaking(0);
        solver.options().setSkolemDepth(-1);
        solver.options().setLogTranslation(2);
        return solver.solve(f, b);
    }
}

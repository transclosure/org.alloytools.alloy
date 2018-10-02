package amalgam.scripting;

import amalgam.examples.BidirTrans;
import amalgam.examples.DataRepair;
import amalgam.examples.KodkodExample;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

public class EvalObjectives {

    public static void main(String[] args) {
        KodkodExample spec;
        SATFactory solver;
        Bounds lowb;
        Bounds highb;

        spec = new DataRepair();
        solver = SATFactory.Z3;
        lowb = spec.bounds(20);
        highb = spec.bounds(40);
        time("CACHE WARM", spec.verifyformula(), lowb, solver, 10);
        time("datarepair 20 z3", spec.verifyformula(), lowb, solver, 3);
        time("datarepair 40 z3", spec.verifyformula(), highb, solver, 3);
        lowb = spec.target(lowb);
        highb = spec.target(highb);
        time("datarepair 20 z3+target", spec.verifyformula(), lowb, solver, 3);
        time("datarepair 40 z3+target", spec.verifyformula(), highb, solver, 3);

        spec = new BidirTrans();
        solver = SATFactory.Z3;
        lowb = spec.bounds(8);
        highb = spec.bounds(12);
        time("bidirtrans 8 z3", spec.verifyformula(), lowb, solver, 3);
        time("bidirtrans 12 z3", spec.verifyformula(), highb, solver, 3);
        lowb = spec.target(lowb);
        highb = spec.target(highb);
        time("bidirtrans 8 z3+target", spec.verifyformula(), lowb, solver, 3);
        time("bidirtrans 12 z3+target", spec.verifyformula(), highb, solver, 3);
    }

    private static void time(String name, Formula f, Bounds b, SATFactory s, int outof) {
        System.out.println(name);
        System.out.println("--------------------");
        double transtotal = 0;
        double solvetotal = 0;
        for(int i=0; i<outof; i++) {
            Solution sol = exec(f, b, s);
            String sat = sol.sat() ? "sat" : "unsat";
            long trans = sol.stats().translationTime();
            long solve = sol.stats().solvingTime();
            System.out.println(trans + "\t"+ solve + "\t" + sat);
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

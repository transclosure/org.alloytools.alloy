package scripting;

import examples.BidirTrans;
import examples.DataRepair;
import examples.KodkodExample;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

public class Evaluation {

    public static void main(String[] args) {
        KodkodExample spec;
        SATFactory solver;

        spec = new DataRepair();
        solver = SATFactory.Z3;
        Bounds lowb = spec.bounds(20);
        Bounds highb = spec.bounds(100);
        exec(spec.formula(), lowb, solver);
        //exec(spec.formula(), highb, solver); timeout!
        lowb.boundTargets(spec.targets(lowb));
        highb.boundTargets(spec.targets(highb));
        //exec(spec.formula(), lowb, solver);
        //exec(spec.formula(), highb, solver);

        spec = new BidirTrans();
        solver = SATFactory.Z3;
        exec(spec.formula(), spec.bounds(8), solver);
        exec(spec.formula(), spec.bounds(20), solver);
    }

    private static void exec(Formula f, Bounds b, SATFactory s) {
        final Solver solver = new Solver();
        solver.options().setSolver(s);
        solver.options().setSymmetryBreaking(0);
        solver.options().setSkolemDepth(-1);
        solver.options().setLogTranslation(2);
        final Solution sol = solver.solve(f, b);
        System.out.println(sol);
    }
}

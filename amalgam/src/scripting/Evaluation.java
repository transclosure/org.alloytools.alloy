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
        Bounds lowb;
        Bounds highb;

        // FIXME cache warming

        spec = new DataRepair();
        solver = SATFactory.Z3;
        lowb = spec.bounds(20);
        highb = spec.bounds(100);
        System.out.println(time(spec.formula(), lowb, solver, 1));
        //System.out.println(time(spec.formula(), highb, solver, 1)); timeout!
        lowb.boundTargets(spec.targets(lowb));
        highb.boundTargets(spec.targets(highb));
        System.out.println(time(spec.formula(), lowb, solver, 1));
        //System.out.println(time(spec.formula(), highb, solver, 1)); timeout!

        spec = new BidirTrans();
        solver = SATFactory.Z3;
        lowb = spec.bounds(8);
        highb = spec.bounds(20);
        System.out.println(time(spec.formula(), lowb, solver, 1));
        System.out.println(time(spec.formula(), highb, solver, 1));
        lowb.boundTargets(spec.targets(lowb));
        highb.boundTargets(spec.targets(highb));
        System.out.println(time(spec.formula(), lowb, solver, 1));
        //System.out.println(time(spec.formula(), highb, solver, 1)); timeout!
    }

    private static double time(Formula f, Bounds b, SATFactory s, int outof) {
        double total = 0;
        for(int i=0; i<outof; i++) {
            Solution sol = exec(f, b, s);
            total += sol.stats().solvingTime();
        }
        return total / outof;
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

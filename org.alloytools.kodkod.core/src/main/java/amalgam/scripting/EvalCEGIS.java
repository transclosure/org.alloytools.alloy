package amalgam.scripting;

import amalgam.examples.HomeNet;
import amalgam.examples.KodkodExample;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;

public class EvalCEGIS {

    public static void main(String[] args) {
        KodkodExample spec = new HomeNet();
        SATFactory solver = SATFactory.Z3;
        final int n = 4;

        // CEGIS loop
        int i = 0;
        Bounds initial = spec.bounds(n);
        Formula refinement = Formula.TRUE;
        Instance synth = null;
        Bounds restriction = initial;
        Instance verify = null;
        while(verify==null && i++<10) {
            // refine and synthesize
            refinement = spec.refine(refinement, synth);
            synth = time("synth"+i, refinement, initial, solver);
            // restrict and verify
            restriction = spec.restrict(restriction, synth);
            verify = time("verify"+i, spec.formula(), restriction, solver);
        }
    }

    private static Instance time(String name, Formula f, Bounds b, SATFactory s) {
        System.out.println(name);
        System.out.println("--------------------");
        double transtotal = 0;
        double solvetotal = 0;
        //
        Solution sol = exec(f, b, s);
        String sat = sol.sat() ? "sat" : "unsat";
        long trans = sol.stats().translationTime();
        long solve = sol.stats().solvingTime();
        System.out.println(trans + "\t"+ solve + "\t" + sat);
        if(sol.sat()) {
            System.out.println(sol.instance().toPrettyString());
        } else {
            System.out.println("UNSAT");
        }
        transtotal += trans;
        solvetotal += solve;
        //
        System.out.println("--------------------");
        System.out.println("");
        return sol.sat() ? sol.instance() : null;
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

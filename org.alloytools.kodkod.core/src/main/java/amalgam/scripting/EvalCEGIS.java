package amalgam.scripting;

import amalgam.examples.HomeNet;
import amalgam.examples.KodkodExample;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.SolutionIterator;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;

import java.util.Iterator;

public class EvalCEGIS {

    public static void main(String[] args) {
        KodkodExample spec = new HomeNet();
        SATFactory solver = SATFactory.Z3;
        final int n = 5;
        System.out.println(cegis(spec, solver, n));
        System.out.println("Time: "+transtotal+" "+solvetotal);
    }

    private static String cegis(KodkodExample spec, SATFactory solver, int n) {
        int i = 0;
        Bounds synthbounds = spec.bounds(n);
        Solution synth;
        Bounds verifybounds = synthbounds.clone();
        Solution verify;
        while(i++<1000) {
            // synthesize
            synth = exec(spec.synthformula(), synthbounds, solver);
            stats(synth);
            if(synth.sat()) System.out.println(synth.instance().toPrettyString());
            else return "UNSAT";
            // restrict (synth output as kodkod partial instance)
            verifybounds = spec.restrict(verifybounds, synth.instance());
            // verify
            verify = exec(spec.formula(), verifybounds, solver);
            stats(verify);
            if(verify.sat()) return "SAT";
            // refine (synth input as solver side effect)
            synthbounds = spec.refine(synthbounds, synth.instance());
        }
        return "TIMEOUT";
    }

    private static int transtotal = 0;
    private static int solvetotal = 0;
    private static void stats(Solution sol) {
        String sat = sol.sat() ? "sat" : "unsat";
        long trans = sol.stats().translationTime();
        long solve = sol.stats().solvingTime();
        System.out.println(trans + "\t"+ solve + "\t" + sat);
        transtotal += trans;
        solvetotal += solve;
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

package amalgam.scripting;

import amalgam.examples.HomeNet;
import amalgam.examples.KodkodExample;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

public class EvalCEGIS {

    public static void main(String[] args) {
        KodkodExample spec = new HomeNet();
        SATFactory solver = SATFactory.Z3;
        final int n = 5;
        final int limit = 1000;
        System.out.println(cegis(spec, solver, n, limit));
        System.out.println("Time trans+solve=total (ms): "+transtotal+"+"+solvetotal+"="+(transtotal+solvetotal));
    }

    private static String cegis(KodkodExample spec, SATFactory solver, int n, int loopLimit) {
        int i = 0;
        Bounds synthbounds = spec.bounds(n);
        Solution synth;
        Bounds verifybounds = synthbounds.clone();
        Solution verify;
        while(i++<loopLimit) {
            // synthesize
            synth = exec(spec.synthformula(), synthbounds, solver);
            stats(synth, "synth: ");
            if(synth.sat()) System.out.println(synth.instance().toPrettyString());
            else return "Synthesis step failed with UNSAT";
            // restrict (synth output as kodkod partial instance)
            verifybounds = spec.restrict(verifybounds, synth.instance());
            // verify
            verify = exec(spec.formula().not(), verifybounds, solver);
            stats(verify, "verify: ");
            if(verify.unsat()) return "Verification step succeeded with UNSAT";
            // refine (synth input as solver side effect)
            synthbounds = spec.refine(synthbounds, synth.instance(), verify.instance());
        }
        return "TIMEOUT: loop limit of "+loopLimit+" exceeded.";
    }

    private static int transtotal = 0;
    private static int solvetotal = 0;
    private static void stats(Solution sol, String prefix) {
        String sat = sol.sat() ? "sat" : "unsat";
        long trans = sol.stats().translationTime();
        long solve = sol.stats().solvingTime();
        System.out.println(prefix+"trans (ms): " + trans + "\tsolve (ms):"+ solve + "\t" + sat);
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

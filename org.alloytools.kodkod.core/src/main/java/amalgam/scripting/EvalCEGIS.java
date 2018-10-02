package amalgam.scripting;

import amalgam.examples.HomeNet;
import amalgam.examples.KodkodExample;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

import java.util.Collection;
import java.util.List;

public class EvalCEGIS {

    public static void main(String[] args) {
        KodkodExample spec = new HomeNet();
        SATFactory solver = SATFactory.Z3;
        final int n = 10;
        final int limit = 1000;
        //System.out.println(cegis(spec, solver, n, limit));
        //System.out.println("Time trans+solve=total (ms): "+transtotal+"+"+solvetotal+"="+(transtotal+solvetotal));

        //System.out.println("==================");
        //System.out.println(naiveSAT(spec, solver, n));

        System.out.println("==================");
        System.out.println(basicCEGIS(spec, solver, n, limit));
    }

    // Naive SAT approach to synthesis (applicable for /this/ example)
    private static String naiveSAT(KodkodExample spec, SATFactory solver, int n) {
        Bounds b = spec.bounds(n);
        Formula f = spec.verifyformula();
        Solution result = exec(f, b, solver);
        stats(result, "naive");
        if(result.sat()) return "synth achieved:"+result.instance();
        else return "synth failed";
    }

    private static String basicCEGIS(KodkodExample spec, SATFactory solver, int n, int loopLimit) {
        int i = 0;
        Bounds synthbounds = spec.bounds(n);
        final Bounds verifybounds = synthbounds.clone().unmodifiableView();
        Solution synth, verify;

        Formula synthformula = spec.synthformula();   // the "system model", free of goals
        Collection<KodkodExample.SynthGoal> goals = spec.goals(); // collection of properties phi

        System.out.println("Starting with bounds: "+synthbounds);

        while(i++<loopLimit) {
            // synthesize
            synth = exec(synthformula, synthbounds, solver);
            stats(synth, "synth: ");
            if(synth.unsat()) return "FAILURE, synth unsat; f was: "+synthformula;
            // TODO: hardcoding name of synth func to aid debugging
            else System.out.println(synth.instance().relationTuples().get(synthbounds.findRelByName("connected")));

            // full restrict and verify (for each phi)
            boolean allpassed = true;
            for(KodkodExample.SynthGoal g : goals) {
                Formula phi = g.boundformula(); // all universals plugged in
                // TODO: technically, don't need to invoke solver here; can just evaluate, but we need bindings
                verify = exec(phi.not(), spec.restrict(verifybounds, synth.instance(), false), solver);
                stats(verify, "verify: ");
                if (verify.sat()) {
                    System.out.println("phi failed: "+phi);
                    // augment synthesis formula
                    // Setup for next iteration: enforce property phi, instantiated with CE bindings, holds in synth result
                    // Here is where we need the Kodkod-level constants
                    Formula instantiatedphi = g.instantiateWithCE(verify.instance(), verifybounds);
                    System.out.println("Synth formula enhanced with: "+instantiatedphi);
                    synthformula = synthformula.and(instantiatedphi);
                    allpassed = false;
                }
                // otherwise, phi passes, move on to next one
            }
            if(allpassed) return "SUCCESS, all phis passed";
        }
        return "TIMEOUT: loop limit of "+loopLimit+" exceeded.";
    }

    private static String cegis(KodkodExample spec, SATFactory solver, int n, int loopLimit) {
        int i = 0;
        Bounds synthbounds = spec.bounds(n);
        final Bounds verifybounds = synthbounds.clone().unmodifiableView();
        Solution synth, verify;
        while(i++<loopLimit) {
            // synthesize
            synth = exec(spec.synthformula(), synthbounds, solver);
            stats(synth, "synth: ");
            if(synth.unsat()) return "FAILURE, synth unsat";
            else System.out.println(synth.instance().toPrettyString());
            // full restrict and verify
            verify = exec(spec.verifyformula().not(), spec.restrict(verifybounds, synth.instance(), false), solver);
            stats(verify, "verify: ");
            if(verify.unsat()) return "SUCCESS, verify unsat";
            // skeleton restrict and refine (sat=reliable synth witness, unsat=unreliable synth skeleton)
            verify = exec(spec.verifyformula(), spec.restrict(verifybounds, synth.instance(), true), solver);
            stats(verify, "witness: ");
            if(verify.sat()) synthbounds = spec.refine(synthbounds, synth.instance(), verify.instance());
            else synthbounds = spec.refine(synthbounds, synth.instance(), null);
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
        //solver.options().setSkolemDepth(-1);
        solver.options().setSkolemDepth(0); // TODO: Tim turned this back on for CE extraction; any issues?
        solver.options().setLogTranslation(2);
        return solver.solve(f, b);
    }
}

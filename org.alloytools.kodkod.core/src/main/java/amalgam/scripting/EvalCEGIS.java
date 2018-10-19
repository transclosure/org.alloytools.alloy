package amalgam.scripting;

import amalgam.examples.RoomHeat;
import amalgam.examples.KodkodExample;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;

import java.util.Collection;

public class EvalCEGIS {

    public static void main(String[] args) {
        KodkodExample spec = new RoomHeat();
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

        spec.verifyformula(); // dummy call to make sure goal variables are initialized
        Formula synthformula = spec.synthformula();   // the "system model", free of goals
        Collection<KodkodExample.SynthGoal> goals = spec.goals(); // collection of properties phi

        System.out.println("Starting with bounds: "+synthbounds);

        while(i++<loopLimit) {
            // synthesize
            System.out.println("--------------------------");
            synth = exec(synthformula, synthbounds, solver);
            stats(synth, "synth: ");
            if(synth.unsat()) return "FAILURE, synth unsat in "+i+" iterations.";
            else {
                // TODO: hardcoding name of synth func to aid debugging
                TupleSet T = synth.instance().relationTuples().get(synthbounds.findRelByName("this/Config.T"));
                TupleSet F = synth.instance().relationTuples().get(synthbounds.findRelByName("this/Config.F"));
                TupleSet G = synth.instance().relationTuples().get(synthbounds.findRelByName("this/Config.G"));
                TupleSet heats = synth.instance().relationTuples().get(synthbounds.findRelByName("this/Time.heat"));
                TupleSet temps = synth.instance().relationTuples().get(synthbounds.findRelByName("this/Time.temp"));
                System.out.println("this/Config.T = "+T);
                System.out.println("this/Config.F = "+F);
                System.out.println("this/Config.G = "+G);
                System.out.println("this/Time.heat = "+heats);
                System.out.println("this/Time.temp = "+temps);
            }
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
            if(allpassed) return "SUCCESS, all phis passed in "+i+" iterations.";
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
        solver.options().setBitwidth(8); // FIXME ASSUME 8
        solver.options().setNoOverflow(true); // disallow integer overflow (or #R = 7 can overflow)
        solver.options().setSymmetryBreaking(0);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSkolemDepth(0);
        solver.options().setLogTranslation(2);
        return solver.solve(f, b);
    }
}

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
        final int n = 4;
        // CEGIS loop
        int i = 0;
        Bounds initial = spec.bounds(n);
        // no way to state naive negation as a formula
        // using solution iterator instead of KodkodExample.refine() method
        // effectively means: clause learn not-model
        Iterator<Solution> synths = exec(Formula.TRUE, initial, solver);
        Solution synth;
        Bounds restriction = initial;
        Solution verify = null;
        while(verify==null && synths.hasNext() && i++<100) {
            // refine and synthesize
            synth = synths.next();
            stats(synth);
            if(synth.sat()) System.out.println(synth.instance().toPrettyString());
            // restrict and verify
            restriction = spec.restrict(restriction, synth.instance());
            verify = exec(spec.formula(), restriction, solver).next();
            stats(verify);
            if(verify.unsat()) verify = null;
        }
        if(verify!=null) {
            System.out.println("SAT");
        } else if (synths.hasNext()) {
            System.err.println("TIMEOUT");
        } else {
            System.err.println("UNSAT");
        }
    }

    private static void stats(Solution sol) {
        String sat = sol.sat() ? "sat" : "unsat";
        long trans = sol.stats().translationTime();
        long solve = sol.stats().solvingTime();
        System.out.println(trans + "\t"+ solve + "\t" + sat);
    }
    private static Iterator<Solution> exec(Formula f, Bounds b, SATFactory s) {
        final Solver solver = new Solver();
        solver.options().setSolver(s);
        solver.options().setSymmetryBreaking(0);
        solver.options().setSkolemDepth(-1);
        solver.options().setLogTranslation(2);
        return solver.solveAll(f, b);
    }
}

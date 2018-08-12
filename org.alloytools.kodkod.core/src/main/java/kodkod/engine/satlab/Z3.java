package kodkod.engine.satlab;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Relation;
import kodkod.engine.fol2sat.*;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

import com.microsoft.z3.*;
import kodkod.util.ints.IntIterator;

/**
 * AMALGAM smt2 external solver z3
 */
public class Z3 implements SATProver {

    private List<BoolExpr>          vars;
    private int                     clauses;
    private Context                 context;
    private Solver                  solver;
    private boolean                 sat;
    private boolean[]               solution;

    /** CNF -> Z3 **/
    private BoolExpr encode(int lit) {
        int i = Math.abs(lit);
        String var = "VAR_" + i;
        return context.mkBoolConst(var);
    }
    private BoolExpr encode(int[] lits, boolean soft, String id) {
        if(lits.length==1) {
            int i = Math.abs(lits[0]);
            return lits[0]>0 ? vars.get(i) : context.mkNot(vars.get(i));
        } else {
            BoolExpr[] clause = new BoolExpr[lits.length];
            for(int l=0; l<lits.length; l++) {
                int lit = lits[l];
                int i = Math.abs(lit);
                clause[l] = lit>0 ? vars.get(i) : context.mkNot(vars.get(i));
            }
            return context.mkOr(clause);
        }
    }

    /** In-Bound Target -> CNF **/
    public static List<List<Integer>> encode(Bounds bounds, Relation relation, TupleSet target) {
        List<List<Integer>> clauses = new ArrayList<>();
        IntIterator alltuples = bounds.upperBound(relation).indexView().iterator();
        while(alltuples.hasNext()) {
            int lit = alltuples.next();
            Tuple tuple = bounds.universe().factory().tuple(relation.arity(), lit);
            lit = target.contains(tuple) ? lit : -1*lit;
            List<Integer> clause = new ArrayList<>();
            clause.add(lit);
            clauses.add(clause);
        }
        return clauses;
    }
    private void assertTargets(Bounds bounds) {
        int t = 1;
        for(Relation relation : bounds.relations()) {
            TupleSet target = bounds.targetBound(relation);
            if(target!=null) {
                List<List<Integer>> targetclauses = encode(bounds, relation, target);
                for (List<Integer> targetclause : targetclauses) {
                    int[] clause = new int[1];
                    clause[0] = targetclause.get(0);
                    //TODO solver.add(encode(clause, true, "target"+t));
                    t++;
                }
            }
        }
    }

    public Z3() {
        try {
            vars = new ArrayList<>();
            clauses = 0;
            context = new Context();
            solver = context.mkSolver();
        } catch (UnsatisfiedLinkError e) {
            System.err.println("failed to launch z3! build z3 for java and make sure \nlibz3java.so and libz3.so are in your java.library.path");
            System.err.println("java.library.path:="+System.getProperty("java.library.path"));
            throw e;
        }
    }
    @Override
    public int numberOfVariables() {
        return vars.size();
    }
    @Override
    public int numberOfClauses() {
        return clauses;
    }
    @Override
    public void addVariables(int numVars) {
        if (numVars < 0)
            throw new IllegalArgumentException("vars < 0: " + numVars);
        int n = vars.size();
        for (int i = n + 1; i <= n + numVars; i++) {
            BoolExpr var = encode(i);
            vars.add(var);
        }
    }
    @Override
    public boolean addClause(int[] lits) {
        clauses++;
        // naive maxSET: softens top level soft clause
        //boolean naiveMax = lits.length == 1 && FOL2BoolCache.softcache.contains(Math.abs(lits[0]));
        // proper maxSET: softens each subformula of the top-level conjunction
        boolean soft = (lits.length == 2 &&
                (FOL2BoolCache.softcache.contains(Math.abs(lits[0]))
                        || FOL2BoolCache.softcache.contains(Math.abs(lits[1]))));
        if (lits.length == 0) {
            solver.add(context.mkFalse());
        } else {
            solver.add(encode(lits, soft, ""));
        }
        return true;
    }
    @Override
    public void sideEffects(Translation translation) throws SATAbortedException {
        assertTargets(translation.bounds());
    }
    @Override
    public boolean solve(Translation translation) throws SATAbortedException {
        return solve();
    }
    @Override
    public boolean solve() throws SATAbortedException {
        //TODO writeln("(set-option :opt.priority pareto)", smt2);
        sat = solver.check() == Status.SATISFIABLE ? true : false;
        if (sat) {
            Model model = solver.getModel();
            solution = new boolean[vars.size()];
            for(int i=0; i<vars.size(); i++) {
                solution[i] = model.eval(vars.get(i), true).isTrue();
            }
        } else {
            solution = null;
        }
        return sat;
    }
    @Override
    public boolean valueOf(int variable) {
        if (!Boolean.TRUE.equals(sat))
            throw new IllegalStateException();
        if (variable < 1 || variable > vars.size())
            throw new IllegalArgumentException(variable + " !in [1.." + vars + "]");
        return solution[variable - 1];
    }
    @Override
    public void free() {
        context.close();
    }
    @Override
    public ResolutionTrace proof() {
        // TODO z3 proofs
        throw new UnsupportedOperationException("not implemented yet");
    }
    @Override
    public void reduce(ReductionStrategy strategy) {
        // TODO z3 proofs
        throw new UnsupportedOperationException("not implemented yet");
    }
}

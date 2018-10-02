package kodkod.engine.satlab;

import java.io.*;
import java.time.Instant;
import java.time.ZoneId;
import java.util.*;

import kodkod.ast.Relation;
import kodkod.engine.bool.Int;
import kodkod.engine.fol2sat.*;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

import com.microsoft.z3.*;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

/**
 * AMALGAM smt2 external solver z3
 */
public class Z3 implements SATProver {

    private final static boolean    debug = true;
    // kodkod
    private List<BoolExpr>          vars;
    private boolean                 sat;
    private boolean[]               solution;
    private int                     clauses;
    // z3
    private Context                 context;
    private Optimize                solver;


    /** CNF -> Z3 **/
    private BoolExpr encode(int lit) {
        int i = Math.abs(lit);
        String var = "VAR_" + i;
        return context.mkBoolConst(var);
    }
    private void encode(int[] lits, boolean soft, String id) {
        // hard unit / soft unit (target) clauses
        if(lits.length==1) {
            int i = Math.abs(lits[0]);
            BoolExpr clause = null;
            if(lits[0]>0) {
                clause = vars.get(i-1);
            } else {
                clause = context.mkNot(vars.get(i-1));
            }
            if(soft) {
                solver.AssertSoft(clause, 1, id);
            } else {
                solver.Assert(clause);
            }
        }
        // hard / soft clauses
        else {
            BoolExpr[] clause = new BoolExpr[lits.length];
            for (int l = 0; l < lits.length; l++) {
                int lit = lits[l];
                int i = Math.abs(lit);
                clause[l] = lit > 0 ? vars.get(i-1) : context.mkNot(vars.get(i-1));
            }
            if(soft) {
                solver.AssertSoft(context.mkOr(clause), 1, id);
            } else {
                solver.Assert(context.mkOr(clause));
            }
        }
    }
    private void decode() {
        // Params
        Params p = context.mkParams();
        p.add("opt.priority", "pareto");
        solver.setParameters(p);
        // Debug
        if(debug) {
            RandomAccessFile spec = null;
            try {
                String inTemp = File.createTempFile("debug-z3-", Instant.now()+".smt2").getAbsolutePath();
                spec = new RandomAccessFile(inTemp, "rw");
                spec.setLength(0);
                spec.writeBytes(solver.toString());
                spec.close();
            } catch (IOException e) {
                try { spec.close(); } catch (Exception ee) {}
                throw new SATAbortedException(e);
            }
        }
        // Solve
        sat = solver.Check() == Status.SATISFIABLE ? true : false;
        if (sat) {
            Model model = solver.getModel();
            //if(debug) System.out.println(model.toString());
            solution = new boolean[vars.size()];
            for (int i = 0; i < vars.size(); i++) {
                solution[i] = model.eval(vars.get(i), true).isTrue();
            }
        } else {
            solution = null;
        }
    }

    /** In-Bound Target -> CNF **/
    private List<List<Integer>> encode(Translation translation, Relation relation, TupleSet tuples, boolean partial) {
        List<List<Integer>> clauses = new ArrayList<>();
        IntIterator indicies = translation.bounds().upperBound(relation).indexView().iterator();
        IntIterator lits = translation.primaryVariables(relation).iterator();
        while(lits.hasNext()) {
            int lit = lits.next();
            int index = indicies.next();
            Tuple tuple = translation.bounds().universe().factory().tuple(relation.arity(), index);
            lit = tuples.contains(tuple) ? lit : -1 * lit;
            if((partial && lit>0) || !partial) {
                List<Integer> clause = new ArrayList<>();
                clause.add(lit);
                clauses.add(clause);
            }
        }
        return clauses;
    }
    private void assertIncludes(Translation translation) {
        Bounds bounds = translation.bounds();
        int includenum = 1;
        for(Map<Relation,TupleSet> include : bounds.includes) {
            if(debug) System.out.println("Include"+includenum+": "+include);
            for (Relation relation : include.keySet()) {
                TupleSet tuples = include.get(relation);
                List<List<Integer>> includeclauses = encode(translation, relation, tuples, true);
                for (int i=0; i<includeclauses.size(); i++) {
                    List<Integer> includeclause = includeclauses.get(i);
                    int[] clause = new int[1];
                    clause[0] = includeclause.get(0);
                    encode(clause, false, null);
                }
            }
            includenum++;
        }
    }
    private void assertTargets(Translation translation) {
        Bounds bounds = translation.bounds();
        int targetnum = 1;
        for(Map<Relation,TupleSet> target : bounds.targets) {
            if(debug) System.out.println("Target"+targetnum+": "+target);
            for (Relation relation : target.keySet()) {
                TupleSet tuples = target.get(relation);
                List<List<Integer>> targetclauses = encode(translation, relation, tuples, true);
                for (int i=0; i<targetclauses.size(); i++) {
                    List<Integer> targetclause = targetclauses.get(i);
                    int[] clause = new int[1];
                    clause[0] = targetclause.get(0);
                    String id = "target"+targetnum;
                    encode(clause, true, id);
                }
            }
            targetnum++;
        }
    }
    private void assertExcludes(Translation translation) {
        Bounds bounds = translation.bounds();
        int excludenum = 1;
        for(Map<Relation,TupleSet> exclude : bounds.excludes) {
            if(debug) System.out.println("Exclude"+excludenum+": "+exclude);
            List<Integer> notmodel = new ArrayList<>();
            for (Relation relation : exclude.keySet()) {
                TupleSet tuples = exclude.get(relation);
                List<List<Integer>> excludeclauses = encode(translation, relation, tuples, false);
                for (int i=0; i<excludeclauses.size(); i++) {
                    List<Integer> excludeclause = excludeclauses.get(i);
                    notmodel.add(-1*excludeclause.get(0));
                }
            }
            int[] nm = new int[notmodel.size()];
            for(int i=0; i<notmodel.size(); i++) {
                nm[i] = notmodel.get(i);
            }
            encode(nm, false, null);
            excludenum++;
        }
    }

    /** Initialize Z3 */
    public Z3() {
        try {
            vars = new ArrayList<>();
            clauses = 0;
            context = new Context();
            solver = context.mkOptimize();
        } catch (UnsatisfiedLinkError e) {
            throw new SATAbortedException("z3 libs missing from java.library.path:\n"+System.getProperty("java.library.path"), e);
        }
    }

    /** Solver generic functionality */
    @Override
    public void sideEffects(Translation translation) throws SATAbortedException {
        assertIncludes(translation);
        assertTargets(translation);
        assertExcludes(translation);
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
        // empty
        if (lits.length == 0) {
            solver.Assert(context.mkFalse());
        }
        else {
            Set<Integer> clause = new LinkedHashSet<>();
            for(int lit : lits) clause.add(lit);
            // soft clause
            if(FOL2BoolCache.softcache.containsKey(clause)) {
                encode(lits, true, FOL2BoolCache.softcache.get(clause));
            }
            // hard clause
            else {
                encode(lits, false, null);
            }
        }
        return true;
    }
    @Override
    public boolean solve(Translation translation) throws SATAbortedException {
        return solve();
    }
    @Override
    public boolean solve() throws SATAbortedException {
        decode();
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
        // TODO decode z3 proofs
        throw new UnsupportedOperationException("not implemented yet");
    }
    @Override
    public void reduce(ReductionStrategy strategy) {
        // TODO decode z3 proofs
        throw new UnsupportedOperationException("not implemented yet");
    }
}

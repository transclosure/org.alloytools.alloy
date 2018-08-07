package kodkod.engine.satlab;

import java.io.*;
import java.util.Iterator;
import java.util.Map;

import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.bool.Int;
import kodkod.engine.fol2sat.*;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import scripting.Toolbox;

import static scripting.Toolbox.*;

/**
 * AMALGAM smt2 external solver z3
 */
public class Z3 implements SATProver {

    private String                  inTemp;
    private RandomAccessFile        smt2;
    private int                     vars, clauses;
    private Translation.Whole       translation;
    private boolean                 sat;
    private boolean[]               solution;

    public Z3() {
        smt2 = null;
        try {
            inTemp = File.createTempFile("kodkod", String.valueOf("z3".hashCode())).getAbsolutePath();
            smt2 = new RandomAccessFile(inTemp, "rw");
            smt2.setLength(0);
        } catch (FileNotFoundException e) {
            throw new SATAbortedException(e);
        } catch (IOException e) {
            close(smt2);
            throw new SATAbortedException(e);
        }
        vars = 0;
        clauses = 0;
    }
    @Override
    public int numberOfVariables() {
        return vars;
    }
    @Override
    public int numberOfClauses() {
        return clauses;
    }
    @Override
    public void addVariables(int numVars) {
        if (numVars < 0)
            throw new IllegalArgumentException("vars < 0: " + numVars);
        for (int i = vars + 1; i <= vars + numVars; i++) {
            writeln(desugar(i), smt2);
        }
        vars += numVars;
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
            writeln("(assert false)", smt2);
        } else {
            writeln(desugar(lits, soft), smt2);
        }
        return true;
    }
    @Override
    public boolean solve(Translation translation) throws SATAbortedException {
        if(translation==null) throw new SATAbortedException("translation given is null");
        this.translation = (Translation.Whole)translation;
        return solve();
    }
    @Override
    public boolean solve() throws SATAbortedException {
        writeln("(push)", smt2);
        writeln("(check-sat)", smt2);
        writeln("(get-model)", smt2);
        try {
            // run z3 on the smt2 file
            Process p = null;
            final String[] command = new String[3];
            command[0] = "z3";
            command[1] = "-smt2";
            command[2] = inTemp;
            p = Runtime.getRuntime().exec(command);
            BufferedReader out = new BufferedReader(new InputStreamReader(p.getInputStream()));
            // parse the output into a sat/solution
            String line;
            while (!(line = out.readLine()).contains("sat")) {}
            sat = line.equals("sat");
            if (sat) {
                solution = new boolean[vars];
                int i = -1;
                while ((line = out.readLine()) != null) {
                    if (line.contains("(define-fun VAR_")) {
                        i = Integer.parseInt(line.split("VAR_")[1].split(" ")[0]);
                        assert 0 < i && i <= vars;
                    } else if (line.contains("true")) {
                        assert 0 < i && i <= vars;
                        solution[i - 1] = true;
                        i = -1;
                    } else if (line.contains("false")) {
                        assert 0 < i && i <= vars;
                        solution[i - 1] = false;
                        i = -1;
                    }
                }
            } else {
                solution = null;
            }
        } catch (IOException e) {
            throw new SATAbortedException(e);
        }
        writeln("(pop)", smt2);
        return sat;
    }
    @Override
    public boolean valueOf(int variable) {
        if (!Boolean.TRUE.equals(sat))
            throw new IllegalStateException();
        if (variable < 1 || variable > vars)
            throw new IllegalArgumentException(variable + " !in [1.." + vars + "]");
        return solution[variable - 1];
    }
    @Override
    public void free() {
        close(smt2);
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

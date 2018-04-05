package kodkod.engine.satlab;

import java.io.BufferedReader;
import java.io.Closeable;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.RandomAccessFile;

/**
 * AMALGAM smt2 external solver z3
 */
public class Z3 implements SATProver {

    private String           inTemp;
    private RandomAccessFile smt2;
    private int              vars, clauses;
    private boolean          sat;
    private boolean[]        solution;

    private static void close(Closeable closeable) {
        try {
            if (closeable != null)
                closeable.close();
        } catch (IOException e) {} // ignore
    }

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

    private void writeln(String line) {
        try {
            smt2.writeBytes(line + "\n");
        } catch (IOException e) {
            close(smt2);
            throw new SATAbortedException(e);
        }
    }

    @Override
    public void addVariables(int numVars) {
        if (numVars < 0)
            throw new IllegalArgumentException("vars < 0: " + numVars);
        for (int i = vars + 1; i <= vars + numVars; i++) {
            String v = "v" + i;
            writeln("(declare-const " + v + " Bool)");
        }
        vars += numVars;
    }

    @Override
    public boolean addClause(int[] lits) {
        clauses++;
        if (lits.length == 0) {
            writeln("(assert false)");
        } else {
            String clause = "(assert (or";
            for (int lit : lits) {
                int i = Math.abs(lit);
                String l = lit > 0 ? "v" + i : "(not v" + i + ")";
                clause += " " + l;
            }
            clause += "))";
            writeln(clause);
        }
        return true;
    }

    @Override
    public boolean solve() throws SATAbortedException {
        writeln("(push)");
        writeln("(check-sat)");
        writeln("(get-model)");
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
            String line = out.readLine();
            sat = line.equals("sat");
            if (sat) {
                solution = new boolean[vars];
                int i = -1;
                while ((line = out.readLine()) != null) {
                    if (line.contains("(define-fun v")) {
                        i = Integer.parseInt(line.split("v")[1].split(" ")[0]);
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
        writeln("(pop)");
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

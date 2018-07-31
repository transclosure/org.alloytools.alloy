package kodkod.engine.satlab;

import java.io.BufferedReader;
import java.io.Closeable;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.RandomAccessFile;
import java.io.StringWriter;

import kodkod.engine.fol2sat.FOL2BoolCache;
import kodkod.engine.fol2sat.Translation;

/**
 * AMALGAM external LINEAR PROGRAMMING solver gurobi
 */
public class Gurobi implements SATProver {

    private String           inTemp;
    private RandomAccessFile python;
    private int              vars, clauses;
    private boolean          sat;
    private boolean[]        solution;

    private static void close(Closeable closeable) {
        try {
            if (closeable != null)
                closeable.close();
        } catch (IOException e) {} // ignore
    }

    private void writeln(String line) {
        try {
            python.writeBytes(line + "\n");
        } catch (IOException e) {
            close(python);
            throw new SATAbortedException(e);
        }
    }

    public Gurobi() {
        python = null;
        try {
            inTemp = File.createTempFile("kodkod", String.valueOf("Gurobi".hashCode())).getAbsolutePath();
            python = new RandomAccessFile(inTemp, "rw");
            python.setLength(0);
        } catch (FileNotFoundException e) {
            throw new SATAbortedException(e);
        } catch (IOException e) {
            close(python);
            throw new SATAbortedException(e);
        }
        vars = 0;
        clauses = 0;
        writeln("from gurobiAPI import *");
        writeln("");
        writeln("spec = GurobiSpec(\"kodkod\")");
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
        if (numVars < 0) {
            throw new IllegalArgumentException("vars < 0: " + numVars);
        }
        for (int i = vars + 1; i <= vars + numVars; i++) {
            String v = "v" + i;
            writeln("spec.addVariable(\""+ v + "\")");
        }
        vars += numVars;
    }

    @Override
    public boolean addClause(int[] lits) {
        clauses++;
        String clause = "spec.addClause([";
        for (int lit : lits) {
            int i = Math.abs(lit);
            String l = lit > 0 ? "v" + i : "!v" + i;
            clause += "\"" + l + "\", ";
        }
        clause = clause.substring(0, clause.length()-2);
        clause += "])";
        writeln(clause);
        return true;
    }

    @Override
    public boolean solve() throws SATAbortedException {
        String solveline = "spec.solve()";
        writeln(solveline);
        String sol = "";
        try {
            // run Gurobi on the python file
            Process p = null;
            final String[] command = new String[2];
            command[0] = "python3";
            command[1] = inTemp;
            p = Runtime.getRuntime().exec(command);
            BufferedReader out = new BufferedReader(new InputStreamReader(p.getInputStream()));
            // parse the output into a sat/solution
            String line;
            while (!(line = out.readLine()).contains("SAT")) {}
            sat = line.equals("SAT");
            if (sat) {
                solution = new boolean[vars];
                int i = -1;
                while ((line = out.readLine()) != null) {
                    sol += line + "\n";
                    // parse variable
                    if (line.startsWith("v")) {
                        i = Integer.parseInt(line.split("v")[1].split(" = ")[0]);
                        assert 0 < i && i <= vars;
                        // parse value
                        if (line.contains("1.0")) {
                            assert 0 < i && i <= vars;
                            solution[i - 1] = true;
                            i = -1;
                        } else if (line.contains("0.0")) {
                            assert 0 < i && i <= vars;
                            solution[i - 1] = false;
                            i = -1;
                        } else {
                            throw new RuntimeException("unknown variable value");
                        }
                    }
                }
            } else {
                solution = null;
            }
            python.setLength(python.length() - solveline.length() - 1);
        } catch (Exception e) {
            StringWriter w = new StringWriter();
            PrintWriter pw = new PrintWriter(w);
            e.printStackTrace(pw);
            pw.flush();
            throw new SATAbortedException(w.toString()+"\n\n\n"+sol);
        }
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
        close(python);
    }

    @Override
    public ResolutionTrace proof() {
        // TODO Gurobi proofs
        throw new UnsupportedOperationException("not implemented yet");
    }

    @Override
    public void reduce(ReductionStrategy strategy) {
        // TODO Gurobi proofs
        throw new UnsupportedOperationException("not implemented yet");
    }

    @Override
    public boolean solve(Translation.Whole translation) throws SATAbortedException {
        return solve();
    }
}

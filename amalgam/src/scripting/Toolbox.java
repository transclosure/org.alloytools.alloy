package scripting;

import kodkod.ast.Relation;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

import java.io.Closeable;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class Toolbox {

    /** i/o **/
    public static void close(Closeable closeable) {
        try {
            if (closeable != null)
                closeable.close();
        } catch (IOException e) {} // ignore
    }
    public static void writeln(String line, RandomAccessFile file) {
        try {
            file.writeBytes(line + "\n");
        } catch (IOException e) {} // ignore
    }

    /** In-Bound Target -> CNF **/
    public static List<List<Integer>> desugar(Translation translation, Relation relation, TupleSet target) {
        List<List<Integer>> clauses = new ArrayList<>();
        Bounds bounds = translation.bounds();
        TupleSet upper = bounds.upperBound(relation);
        Iterator<Tuple> alltuples = upper.iterator();
        Iterator<Tuple> targettuples = target.iterator();
        while(alltuples.hasNext()) {
            Tuple tuple = alltuples.next();
            boolean targeted = false;
            while(!targeted && targettuples.hasNext()) {
                Tuple targettuple = targettuples.next();
                targeted = tuple.toString().equals(targettuple.toString());
            }
            List<Integer> clause = new ArrayList<>();
            int lit = desugar(translation, relation, tuple);
            lit = targeted ? lit : -1*lit;
            clause.add(lit);
            clauses.add(clause);
        }
        return clauses;
    }
    public static int desugar(Translation translation, Relation relation, Tuple tuple) {
        Bounds bounds = translation.bounds();
        TupleSet upper = bounds.upperBound(relation);
        IntIterator pvars = translation.primaryVariables(relation).iterator();
        Iterator<Tuple> tuples = upper.iterator();
        while(pvars.hasNext()) {
            int pvar = pvars.next();
            if(tuple.toString().equals(tuples.next().toString())) {
                return pvar;
            }
        }
        throw new RuntimeException("why");
    }

    /** CNF -> SMT2 **/
    public static String desugar(int i) {
        String v = "VAR_" + i;
        return "(declare-const " + v + " Bool)";
    }
    public static String desugar(int[] lits, boolean soft) {
        String clause = soft ? "(assert-soft (or" : "(assert (or";
        for (int lit : lits) {
            int i = Math.abs(lit);
            String l = lit > 0 ? "VAR_" + i : "(not VAR_" + i + ")";
            clause += " " + l;
        }
        clause += "))";
        return clause;
    }
}

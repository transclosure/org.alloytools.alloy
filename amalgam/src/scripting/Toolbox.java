package scripting;

import kodkod.ast.Relation;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
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
    public static List<List<Integer>> desugar(Bounds bounds, Relation relation, TupleSet target) {
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

    /** CNF -> SMT2 **/
    public static String desugar(int i) {
        String v = "VAR_" + i;
        return "(declare-const " + v + " Bool)";
    }
    public static String desugar(int[] lits, boolean soft) {
        String clause = soft ? "(assert-soft " : "(assert ";
        if(lits.length==1) {
            int lit = lits[0];
            int i = Math.abs(lit);
            String l = lits[0] > 0 ? "VAR_" + i : "(not VAR_" + i + ")";
            clause += l + ")";
        } else {
            clause += "(or";
            for (int lit : lits) {
                int i = Math.abs(lit);
                String l = lit > 0 ? "VAR_" + i : "(not VAR_" + i + ")";
                clause += " " + l;
            }
            clause += "))";
        }
        return clause;
    }
}

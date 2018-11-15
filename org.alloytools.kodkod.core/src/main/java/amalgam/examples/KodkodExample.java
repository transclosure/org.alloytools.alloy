package amalgam.examples;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;
import java.util.Map;

public interface KodkodExample {
    Bounds bounds(int n);
    Formula formula();
    Map<Relation,TupleSet> targets(Bounds bounds);
}

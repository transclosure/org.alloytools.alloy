package amalgam.examples;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;
import java.util.Map;

public interface KodkodExample {
    // Kodkod
    Bounds bounds(int n);
    Formula formula();
    // CEGIS
    Formula refine(Formula current, Instance refinement);
    Bounds restrict(Bounds current, Instance restriction);
    // Target Oriented
    Map<Relation,TupleSet> target(Bounds bounds);
}

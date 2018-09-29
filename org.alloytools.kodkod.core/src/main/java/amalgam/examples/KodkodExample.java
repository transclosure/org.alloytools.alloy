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
    Formula synthformula();
    Bounds refine(Bounds synthbounds, Instance avoid);
    Bounds restrict(Bounds verifybounds, Instance apply);
    // Target Oriented
    Bounds target(Bounds bounds);
}

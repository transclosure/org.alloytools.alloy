package amalgam.examples;

import kodkod.ast.Formula;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;

public interface KodkodExample {
    // Kodkod
    Bounds bounds(int n);
    Formula formula();
    // CEGIS
    Formula synthformula();
    Bounds refine(Bounds synthbounds, Instance lastsynth, Instance counterexample);
    Bounds restrict(Bounds verifybounds, Instance apply);
    // Target Oriented
    Bounds target(Bounds bounds);
}

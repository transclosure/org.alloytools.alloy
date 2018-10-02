package amalgam.examples;

import kodkod.ast.Formula;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;

public interface KodkodExample {
    // Kodkod
    Bounds bounds(int n);
    Formula verifyformula();
    // CEGIS
    Formula synthformula();
    Bounds restrict(Bounds verifybounds, Instance synth, boolean onlySkeleton);
    Bounds refine(Bounds synthbounds, Instance synth, Instance witness);
    // Target Oriented
    Bounds target(Bounds bounds);
}

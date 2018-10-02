package amalgam.examples;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Variable;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;

import java.util.Collection;
import java.util.List;
import java.util.Map;

public interface KodkodExample {
    // Kodkod
    Bounds bounds(int n);
    Formula verifyformula();
    // CEGIS
    Formula synthformula();
    Collection<SynthGoal> goals();
    Bounds restrict(Bounds verifybounds, Instance synth, boolean onlySkeleton);
    Bounds refine(Bounds synthbounds, Instance synth, Instance verify);
    // Target Oriented
    Bounds target(Bounds bounds);

    interface SynthGoal {
        Map<Variable, Expression> freevars();
        Formula unboundformula();
        Formula boundformula(); // technically not needed, since could construct manually.
        Formula instantiateWithCE(Instance ce, Bounds b);
    }
}


package examples;

import kodkod.ast.Formula;
import kodkod.instance.Bounds;

public interface KodkodExample {
    Bounds bounds(int n);
    Formula formula();
}

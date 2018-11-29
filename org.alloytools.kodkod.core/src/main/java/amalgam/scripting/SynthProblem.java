package amalgam.scripting;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;

import java.util.Collection;
import java.util.Set;

public interface SynthProblem {
    // Relation declarations (use real Relation objects, since we have formulas)

    /** helper relations that help describe the problem (may be any arity) */
    Set<Relation> helperRelations();
    /** state that we can synthesize and deploy (+1 arity for leftmost state column) */
    Set<Relation> deployableRelations();
    /** state we cannot synthesize, only assume or control via system (+1 arity for leftmost state column) */
    Set<Relation> nondeployableRelations();
    /** relations that describe transition events (+1 arity for leftmost state column) */
    Set<Relation> eventRelations();
    /** Constants. E.g., personA, personB, fileX, etc. (should be unary) */
    Set<Relation> constantSingletonRelations();

    // Constraints, axioms, etc.

    /** FOL translation of the temporal goals we have. These should use relations with a leftmost state column.
        The "state" parameter gives the State relation (used for all and exists quantification for G and F etc.) */
    Set<Formula> goals(Relation stateDomain);

    /** Structure, like "this relation is a function" or "A is a subtype of B"
        The "state" parameter gives an expression to construct the fmlas around (usually the State relation) */
    Set<Formula> structuralAxioms(Expression state);

    /** Additional constraints on the initial state. May involve both deployable and non-deployable state relations.
        used to add config-specific goals like "synth'd x should be less than 50", but also
        used to add constraints like "setting (which we don't configure) starts out comfortable".
        "first" is a reference to the first-state relation
       This applies to multiple phases! */
    Set<Formula> additionalInitialConstraintsP1P2(Expression first);

    /** Function that builds a transition relation around pre-supplied state expressions.
        Often post will be pre.next.
        This is similar to just writing an Alloy predicate transition[s: State, s': State]. */
    Formula buildTransition(Expression pre, Expression post);

    /** Pretty printer (for logging, debugging, etc.) */
    String prettyConfigFromSynth(Solution sol);

    /** Construct bounds around a set of concrete states required by the engine.
        For instance, the engine may give only one state tuple for synthesis, two for root-cause extraction,
        or many more for counterexample-generation.
        The problem object has control over what gets provided as bounds and what gets provided as constraints. */
    void setBounds(Bounds bounds, Collection<Tuple> stateExactly);
}
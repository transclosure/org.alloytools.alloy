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
    // FOL translation of the temporal goals we have. These should use the CE relations
    // The "state" parameter gives an expression to construct the fmlas around (usually the State relation)
    Set<Formula> goals(Expression state);

    // Structure, like "this relation is a function" or "A is a subtype of B"
    // The "state" parameter gives an expression to construct the fmlas around (usually the State relation)
    Set<Formula> structuralAxioms(Expression state);

    // Additional constraints on the initial state. May involve both deployable and non-deployable state relations.
    // used to add config-specific goals like "synth'd x should be less than 50", but also
    // used to add constraints like "setting (which we don't configure) starts out comfortable".
    // "first" is a reference to the first-state relation
    // This applies to multiple phases!
    Set<Formula> additionalInitialConstraintsP1P2(Expression first);

    // Relation declarations (use real Relation objects, since we have formulas)
    Set<Relation> helperRelations();        // helper relations that help describe the problem (may be any arity)
    Set<Relation> deployableRelations();    // state that we can synthesize and deploy
    Set<Relation> nondeployableRelations(); // state we cannot synthesize, only assume or control via system
    Set<Relation> allStateRelations();      // union of nondeploy+deploy
    Set<Relation> eventRelations();         // relations that describe transition events
    Set<Relation> constantSingletonRelations(); // personA, personB, fileX, etc. (should be unary)

    // Often post will be pre.next
    Formula buildTransition(Expression pre, Expression post);

    // Pretty printer (for logging, debugging, etc.)
    String prettyConfigFromSynth(Solution sol);

    void setBounds(Bounds bounds, Collection<Tuple> stateExactly);
}
package amalgam.scripting;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;

import java.util.Collection;
import java.util.List;
import java.util.Set;

public interface SynthProblem {
    // FOL translation of the temporal goals we have. These should use the CE relations
    // The "state" parameter gives an expression to construct the fmlas around (usually the State relation)
    Set<Formula> goals(Expression state);
    // Assumptions (about initial state) like "room always starts at 70 degrees"
    // The "first" parameter gives an expression to construct the fmlas around (usually the initial state)
    Set<Formula> initialStateAssumptions(Expression first);
    // Structure, like "this relation is a function" or "A is a subtype of B"
    // The "state" parameter gives an expression to construct the fmlas around (usually the State relation)
    Set<Formula> structuralAxioms(Expression state);
    // Additional constraints on the configuration itself (should use S relations)
    Set<Formula> additionalConfigConstraints();

    // Relation declarations (use real Relation objects, since we have formulas)
    // suffix of S = without the state column; suffix of CE = with the state column
    Set<Relation> helperRelations();        // helper relations that help describe the problem

    Set<Relation> deployableRelationsCE();
    Set<Relation> nondeployableRelationsCE();
    Set<Relation> allStateRelationsCE(); // union of nondeploy+deploy
    Set<Relation> eventRelationsCE();  // relations that describe transition events
    Set<Relation> constantSingletonRelations(); // personA, personB, fileX, etc.

    // Total size of inputs should be eventRelationsCE.size()+2*(deployableRelationsCE.size()+nondeployableRelationsCE.size())
    Formula buildTransition(Expression pre, Expression post);

    String prettyConfigFromSynth(Solution sol);
    void setBounds(Bounds bounds, Collection<Tuple> stateExactly);
}
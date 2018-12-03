package amalgam;

import kodkod.ast.*;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.ExprOperator;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;

import static amalgam.Logger.*;

/**
 * Collection of static constants and helpers for the CEGIS engine
 * DO NOT CREATE STATIC METHODS ANYWHERE ELSE
 */
public class CEGISHelpers {
    // CEGIS options
    public static final SATFactory incrementalSolver = SATFactory.MiniSat;
    public static final SATFactory coreSolver = SATFactory.MiniSatProver;
    public static final int loopLimit = 100;
    public static final int numStates = 5;
    public static final int bitwidth = 8;
    public static final int minInt =  -128;
    public static final int maxInt = 127;
    // CEGIS constants
    public static enum CEGISPHASE {SYNTH, COUNTER, PROXIMAL, ROOT};
    public static final String STR_FIRSTNEXT = "(first . next)";
    public static final Relation state = Relation.unary("State");
    public static final Relation enext = Relation.binary("next");
    public static final Relation first = Relation.unary("first");
    public static final Relation last = Relation.unary("last");

    /**
     * TODO
     * @param targ
     * @param fs
     * @return
     */
    public static boolean isOneOfNegated(Formula targ, Set<Formula> fs) {
        for(Formula f: fs) {
            if(f.not().toString().equals(targ.toString()))
                return true; // TODO: strings again
        }
        return false;
    }

    /**
     * TODO
     * @param f
     * @return
     */
    public static boolean isTraceLiteral(Formula f) {
        // TODO I don't know of a way to do this without instanceof and casting :-(; may need addition to fmla to avoid
        // Could write a visitor, or record the literal formulas instead?
        // This will also remove the goal literals, since they are negations, not comparisons

        if(f instanceof NotFormula) {
            return isTraceLiteral(((NotFormula) f).formula());
        }

        if(!(f instanceof ComparisonFormula)) {
            return false;
        }
        // TODO: this is another kludge because of ad-hoc construction of these literal formulas
        ComparisonFormula cf = (ComparisonFormula) f;
        if(!cf.op().equals(ExprCompOperator.EQUALS) && !cf.op().equals(ExprCompOperator.SUBSET)) {
            return false;
        }

        // Throw out event literals; they aren't useful at this point (kludge; if keeping something we shouldn't, consider
        //   labeling non-deployable configuration and keeping only if deploy/nondeploy relation)
        if(cf.toString().contains("EVENT_")) {
            return false;
        }
        return true;
    }

    /**
     * TODO
     * @param reasons
     * @return
     */
    public static int maxTraceLength(Set<Formula> reasons) {
        int max = 1;
        for(Formula f: reasons) {
            int flen = maxTraceLength(f);
            if(max < flen) max = flen;
        }
        return max;
    }

    /**
     * TODO
     * @param r
     * @return
     */
    public static int maxTraceLength(Formula r) {
        if(r instanceof NotFormula) {
            return maxTraceLength(((NotFormula)r).formula());
        }
        // number of "nexts" following the first, plus one
        if(r instanceof ComparisonFormula) {
            ComparisonFormula cr = (ComparisonFormula) r;
            return Integer.max(maxTraceLength(cr.left()), maxTraceLength(cr.right()));
        } else {
            throw new UnsupportedOperationException(
                    "Tried to process a formula as if it were a state literal, but it wasn't. "+
                    "This may be because the problem definition's goal() set contained formulas with "+
                    "outermost conjunction rather than adding the conjuncts individually to the set. Formula was: "+r);
        }

    }

    /**
     * TODO
     * @param e
     * @return
     */
    public static int maxTraceLength(Expression e) {
        if(e.equals(first)) return 1;
        if(e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) e;
            if(be.right().equals(enext)) return 1 + maxTraceLength(be.left());
            return maxTraceLength(be.left()); // e.g., first.enext.setting
        }
        return 0;
    }

    /**
     * TODO
     * @param f
     * @return
     */
    public static Formula removeDoubleNegation(Formula f) {
        if(f instanceof NotFormula) {
            NotFormula nf = (NotFormula) f;
            Formula ff = nf.formula();
            if(ff instanceof NotFormula) {
                NotFormula nnf = (NotFormula) ff;
                return nnf.formula();
            }
            return f;
        }
        return f;
    }

    /**
     * Build an expression corresponding to the num-th state.
     * @param num
     * @return
     */
    public static Expression buildStateExpr(int num) {
        // Start at one:
        if(num < 1) throw new UnsupportedOperationException("buildStateExpr called with num="+num);
        Expression result = first;
        for(int ii=2;ii<=num;ii++)
            result = result.join(enext);
        return result;
    }

    /**
     * TODO
     * @param e
     * @return
     */
    public static Set<Expression> flattenUnion(Expression e) {
        Set<Expression> result = new HashSet<>();
        // base cases
        if(!(e instanceof BinaryExpression) && !(e instanceof NaryExpression)) {
            result.add(e);
            return result;
        }
        if(e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression)e;
            if (!be.op().equals(ExprOperator.UNION)) {
                result.add(e);
                return result;
            }
            // a union to split up
            result.addAll(flattenUnion(be.left()));
            result.addAll(flattenUnion(be.right()));
            return result;
        }
        NaryExpression ne = (NaryExpression)e;
        if(!ne.op().equals(ExprOperator.UNION)) {
            result.add(e);
            return result;
        }
        for(int ii=0;ii<ne.size();ii++) {
            result.addAll(flattenUnion(ne.child(ii)));
        }
        return result;
    }

    /**
     * TODO
     * @param lhs
     * @param rhs
     * @param domain
     * @return
     */
    public static Set<Formula> desugarInUnion(Expression lhs, Expression rhs, Set<Expression> domain) {
        // Constructed a lhs = rhs expression, where the rhs is a union (possibly nested).
        // Desugar that into a (potentially large) "or" for core purposes
        // ASSUME: lhs is the thing that isnt the union

        Set<Expression> yes = flattenUnion(rhs);
        Set<String> yesStrings = new HashSet<>();
        for(Expression e : yes) {
            yesStrings.add(e.toString());
        }

        // strings again because can't use .equal
        Set<Expression> no = new HashSet<>();
        for(Expression e : domain) {
            if(!yesStrings.contains(e.toString()))
                no.add(e);
        }

        Set<Formula> result = new HashSet<>();
        for(Expression e : yes) {
            result.add(e.in(lhs));
        }
        for(Expression e : no) {
            result.add(e.in(lhs).not());
        }

        output(Level.FINER, "DESUGARING: lhs: "+lhs+"; rhs: "+rhs+"\n"+
                "AS: "+result+"\n"+
                "YES was: "+yes);

        return result;
    }

    /**
     * Extract the thing being joined onto the end of a first.enext.enext... expression
     * @param e
     * @return
     */
    public static Expression findFinalJoin(Expression e) {
        Expression fjoin = null;
        while(e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression)e;
            if(fjoin == null) {
                fjoin = be.right();
                e = be.left();
            }
            else if(be.right().equals(enext)) e = be.left();
            else break;
        }
        return fjoin;
    }

    /**
     * TODO
     * @param f
     * @param depth
     * @return
     */
    public static Formula rewriteStateLiteralDepth(Formula f, int depth) {
        // recur into the formula, replacing
        Expression replaceWith = buildStateExpr(depth);

        if(f instanceof NotFormula) {
            return rewriteStateLiteralDepth(((NotFormula)f).formula(), depth).not();
        } else if(f instanceof ComparisonFormula) {
            ComparisonFormula cf = (ComparisonFormula) f;
            Expression relside, valside;
            if(cf.op().equals(ExprCompOperator.EQUALS)) {
                relside = cf.left(); // first . CE_CONF_allowedTemp = Int[96]+Int[97]
                valside = cf.right();
                output(Level.FINER, "rewriting... relside="+relside+"; valside="+valside+"; final="+findFinalJoin(relside));
                return replaceWith.join(findFinalJoin(relside)).eq(valside);
            }
            else {
                relside = cf.right(); // Int[96] in (first . CE_CONF_allowedTemp)
                valside = cf.left();
                return valside.in(replaceWith.join(findFinalJoin(relside)));
            }

        }
        throw new UnsupportedOperationException("rewriteStateLiteralDepth called with non-negation/comparison: "+f);
    }
}

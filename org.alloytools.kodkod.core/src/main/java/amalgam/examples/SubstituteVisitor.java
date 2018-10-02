package kodkod.ast;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.function.Consumer;

import kodkod.ast.visitor.ReturnVisitor;


public class SubstituteVisitor implements ReturnVisitor<Expression, Formula, Decls, Object> {
    Variable v;
    Expression with;
    
    public SubstituteVisitor(Variable v, Expression with) {
        this.v = v;
        this.with = with;
    }

	@Override
	public Decls visit(Decls decls) {		
		// Note that Decl extends Decls
		Decls result = null;		
		for(Decl d : decls) {			
			Decls newd = d.accept(this);
			if(result == null) {
				result = newd;
			} else {
				result = result.and(newd);
			}
		}
		return result;		
	}
	
	@Override
	public Decl visit(Decl decl) {
		// throw new Exception("Substitution tried to replace variable that is quantified in subexpression: "+v);
		// Don't descend if shadowed
		if(decl.variable().equals(v)) return decl;
		return new Decl(decl.variable(), decl.multiplicity(), decl.expression().accept(this));
	}

	@Override
	public Expression visit(Relation relation) {
		return relation;
	}

	@Override
	public Expression visit(Variable currentVar) {
		if(v.equals(currentVar)) return with; // do substitution
		else return currentVar;               // leave untouched
	}

	@Override
	public Expression visit(ConstantExpression constExpr) {
		return constExpr;
	}

	@Override
	public Expression visit(UnaryExpression unaryExpr) {
		return new UnaryExpression(unaryExpr.op(), unaryExpr.expression().accept(this));
	}

	@Override
	public Expression visit(BinaryExpression binExpr) {
		return new BinaryExpression(binExpr.left().accept(this), binExpr.op(), binExpr.right().accept(this));
	}

	@Override
	public Expression visit(NaryExpression expr) {
		List<Expression> substitutedArgs = new ArrayList<Expression>(expr.arity());
		Iterator<Expression> eitr =  expr.iterator();
        while(eitr.hasNext()) {
            substitutedArgs.add(eitr.next().accept(this));
        }
        return new NaryExpression(expr.op(), substitutedArgs.toArray(null));
	}

	@Override
	public Expression visit(Comprehension comprehension) {
		return new Comprehension(comprehension.decls().accept(this), comprehension.formula().accept(this));
	}

	@Override
	public Expression visit(IfExpression ifExpr) {
		return new IfExpression(ifExpr.condition().accept(this), ifExpr.thenExpr().accept(this), ifExpr.elseExpr().accept(this));
	}

	@Override
	public Expression visit(ProjectExpression project) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Expression visit(IntToExprCast castExpr) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Expression visit(IntConstant intConst) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Expression visit(IfIntExpression intExpr) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Expression visit(ExprToIntCast intExpr) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Expression visit(NaryIntExpression intExpr) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Expression visit(BinaryIntExpression intExpr) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Expression visit(UnaryIntExpression intExpr) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Expression visit(SumExpression intExpr) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Formula visit(IntComparisonFormula intComp) {
		throw new UnsupportedOperationException("substitution");
	}

	@Override
	public Formula visit(QuantifiedFormula quantFormula) {          
        return new QuantifiedFormula(
        		quantFormula.quantifier(),
				quantFormula.decls().accept(this),
				quantFormula.domain().accept(this),
				quantFormula.body().accept(this));
	}

	@Override
	public Formula visit(NaryFormula formula) {
		List<Formula> substitutedArgs = new ArrayList<Formula>(formula.size());
		Iterator<Formula> fitr =  formula.iterator();
        while(fitr.hasNext()) {
            substitutedArgs.add(fitr.next().accept(this));
        }
        return new NaryFormula(formula.op(), substitutedArgs.toArray(null));
	}

	@Override
	public Formula visit(BinaryFormula binFormula) {
		return new BinaryFormula(binFormula.left().accept(this), binFormula.op(), binFormula.right().accept(this));
	}

	@Override
	public Formula visit(NotFormula not) {
		return new NotFormula(not.formula().accept(this));
	}

	@Override
	public Formula visit(ConstantFormula constant) {
		return constant;
	}

	@Override
	public Formula visit(ComparisonFormula compFormula) {
		return new ComparisonFormula(compFormula.left().accept(this), compFormula.op(), compFormula.right().accept(this));
	}

	@Override
	public Formula visit(MultiplicityFormula multFormula) {
		return new MultiplicityFormula(multFormula.multiplicity(), multFormula.expression().accept(this));
	}

	@Override
	public Formula visit(RelationPredicate predicate) {
		return predicate;
	}

	@Override
	public Formula visit(FixFormula f) {
		throw new UnsupportedOperationException("substitution");
	}
}

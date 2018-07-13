from gurobipy import *

# "language" operators
def negate(lit):
	if lit=="":
		return lit
	else:
		return "!"+lit

class GurobiSpec:
	"""syntax to bridge LP (continuous numerics) and SAT (discrete logic) semantics"""
	def __init__(self, name):
		self.name 		= name
		self.theory 	= Model(name)
		self.sugarmap 	= {}

	def sugar(self, name, lit):
		self.sugarmap[name] = lit

	def resugar(self, names):
		# ASSUMES desugar NOT ONE TO MANY
		resugarmap = {v: k for k, v in self.sugarmap.items()}
		for l in lits:
			clause.append(self.sugarmap[l]) 
		return or_(clause)

	def desugar(self, lits):
		clause = []
		for l in lits:
			clause.append(self.sugarmap[l]) 
		return or_(clause)

	def addVariable(self, name, sweeten=True): 
		b = self.theory.addVar(lb=0.0, ub=1.0, vtype=GRB.BINARY, name=name)
		nb = self.theory.addVar(lb=0.0, ub=1.0, vtype=GRB.BINARY, name=negate(name))
		self.theory.addConstr(b + nb == 1.0)
		if sweeten:
			self.sugar(name,b)
			self.sugar(negate(name), nb)
		return b

	def addClause(self, clause):
		c = self.addVariable("", sweeten=False)
		self.theory.addConstr(c == self.desugar(clause), "")
		self.theory.addConstr(c == 1.0, "")

	def checksat(self):
		sat = False
		status = self.theory.getAttr(GRB.Attr.Status)
		if status == GRB.INF_OR_UNBD:
			status = "INFINITE OR UNBOUNDED"
		elif status == GRB.INFEASIBLE:
			status = "INFEASIBLE"
		elif status == GRB.UNBOUNDED:
			status = "UNBOUNDED"
		elif status != GRB.OPTIMAL:
			status = "Optimization was stopped with status "+status
		elif status == GRB.OPTIMAL:
			status = "OPTIMAL"
			sat = True
		else:
			status = "UNKNOWN"
		return sat

	def getmodel(self):
		for n in self.sugarmap.keys():
			print(n, "=", self.sugarmap[n].x)

	def solve(self):
		try:
			self.theory.write(self.name+".mps")
			self.theory.write(self.name+".lp")
			self.theory.optimize()
			if self.checksat(): 
				print("SAT")
				self.getmodel()
			else:
				print("UNSAT")
		except GurobiError as e:
			print("ERROR")
			print('Error code ' + str(e.errno) + ": " + str(e))
		except AttributeError:
			print("ERROR")
			print('Encountered an attribute error')

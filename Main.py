StatementParenthesis=True

_condenseIter=lambda x:([x] if not hasattr(x,"__iter__") else x)
_flatten=lambda *x:[e for a in x for e in (_flatten(*a) if hasattr(a,"__iter__") else (a,))]

class Rule:
	def __init__(self,stateOut,conditions=[],name=None):
		self.stateOut=stateOut
		self.conditions=conditions
		self.name=name
		
	def __call__(self,statement,pool):
		for cond in self.conditions:
			if not cond(statement,pool):
				return(None)
		return([k%self for k in _condenseIter(self.stateOut(*statement.ruleParameters,pool))])

	def __repr__(self):
		return(f"Rule[{self.name}]")

class Operator:
	Operators={}
	def __init__(self,name,symbols,rules,syntax=None,truthEvaluation=lambda a,b:True):
		self.name=name
		if (not hasattr(symbols,"__iter__")) or type(symbols)==str:
			symbols=[symbols]
		self.symbols=symbols
		self.rules=rules
		self.syntax=f"{{0}}{symbols[0]}{{1}}"
		if syntax!=None:self.syntax=syntax
		for sym in self.symbols:self.__class__.Operators[sym]=self
	
	def makeSyntax(self,statements):
		return(self.syntax.format(*statements))

	def __repr__(self):
		return(self.name)

class Variable:
	def __init__(self,name):
		self.name=name
	
	def __repr__(self):
		return(self.name)

class Statement:
	def __init__(self,var,name):
		self.parents=[None]
		self.operator=Operators.NOPERATOR
		self.variable=var
		self.name=name
		self.statements=[self]
		self.parentRule=None
	
	@property
	def ruleParameters(self):
		return(self.statements,self.operator,self)

	@property
	def parentLayers(self):
		if self.parents==[None]:return(0)
		return(max([v.parentLayers+1 for v in self.parents]))

	def setVariable(self,newVar):
		self.variable=newVar

	def returnRules(self,pool):
		return([item for lis in [v for v in [r(self,pool) for r in self.operator.rules] if v!=None] for item in _condenseIter(lis)])
	
	def __repr__(self):
		if StatementParenthesis:
			return(f"{self.name}({self.variable})")
		return(f"{self.name}{self.variable}")
	
	def __eq__(self,other):
		if type(other)!=type(self):return(False)
		if self.variable==other.variable and self.name==other.name:return(True)
		return(False)

	def __and__(self,other):
		if not isinstance(other,Statement):raise(TypeError(f"Unsupported type {type(other)}"))
		return(StatementFunc([self,other],Operators.AND))
	
	def __invert__(self):
		if self.operator==Operators.NOT:return(self.statements[0])
		return(StatementFunc(self,Operators.NOT))
	
	def __or__(self,other):
		if not isinstance(other,Statement):raise(TypeError(f"Unsupported type {type(other)}"))
		return(StatementFunc([self,other],Operators.OR))
		
	def __gt__(self,other):
		if not isinstance(other,Statement):raise(TypeError(f"Unsupported type {type(other)}"))
		return(StatementFunc([self,other],Operators.IMPLICATION))

	def __floordiv__(self,other):
		if not isinstance(other,Statement):raise(TypeError(f"Unsupported type {type(other)}"))
		return(StatementFunc([self,other],Operators.EQUIVILANCE))

	def _copy(self):
		nw=self.__new__(self.__class__)
		nw.__dict__.update(self.__dict__)
		return(nw)

	def __xor__(self,parents):
		if not hasattr(parents,"__iter__"):parents=[parents]
		nw=self._copy()
		nw.parents=parents
		return(nw)

	def __mod__(self,rule):
		nw=self._copy()
		nw.parentRule=rule
		return(nw)

class StatementFunc(Statement):
	def __init__(self,statements,operator):
		self.statements=_condenseIter(statements)
		self.operator=operator
		self.parents=[None]
		self.parentRule=None
	
	def __eq__(self,other):
		if type(other)!=type(self):return(False)
		if self.operator==other.operator and self.statements==other.statements:return(True)

	def __repr__(self):
		ret=[]
		for s in self.statements:
			if type(s)==type(self):
				if len(s.statements)>1:
					ret.append(f"({repr(s)})")
					continue
			ret.append(repr(s))
		return(self.operator.makeSyntax(ret))

class Pool:
	def __init__(self,propositions):
		self.propositions=propositions
		self.pool=list(propositions)
		self.initialPool=list(propositions)
	
	def append(self,newObject):
		if not (newObject in self.pool):
			self.pool.append(newObject)
		return(self)

	def addPool(self,statement):
		for st in statement.returnRules(self):
			self.append(st)

	def checkForConclusion(self,conclusion):
		for ob in self.pool:
			if ob==conclusion:
				return(ob)
		return(None)

	def fullPool(self):
		for item in self.pool.copy():
			self.addPool(item)

	def completePool(self):
		prevpool=self.pool.copy()
		self.fullPool()
		newpool=self.pool.copy()
		while prevpool!=newpool:
			prevpool=newpool
			self.fullPool()
			newpool=self.pool.copy()

	def iFullPool(self):
		poolIterations=[]
		i=1
		prevpool=[]
		newpool=[st for st in self.pool if st.parentLayers<i]
		while prevpool!=newpool:
			poolIterations.append(newpool)
			prevpool=newpool
			i+=1
			newpool=[st for st in self.pool if st.parentLayers<i]
		return(poolIterations)

	def getValue(self,item):
		for ob in self.pool:
			if ob==item:
				return(ob)
		return(None)
	
	def getValueMatch(self,matchLambda):
		ret=[]
		for ob in self.pool:
			try:
				if matchLambda(ob):
					ret.append(ob)
			except Exception as e:pass
		return(ret)

	def proof(self,conclusion):
		concluded=self.checkForConclusion(conclusion)
		if concluded==None:
			return(None)
		proof=list(enumerate(self.initialPool))
		paren=lambda x:_flatten([[*paren(b),b] if b.parents!=[None] else b for b in x.parents])
		steps=[p for p in paren(concluded) if p not in self.initialPool][::-1]
		return(proof+steps)

class Inspecific:
	X=Variable(name="x")
	Y=Variable(name="y")
	Z=Variable(name="z")

class Rules:
	_impl=lambda st,op,full,p:((~st[0])|st[1])^full
	_sym=lambda st,op,full,p:StatementFunc([st[1],st[0]],op)^full
	_rimpl=lambda st,op,full,p:(~st[0]>st[1])^full
	_equiv1=lambda st,op,full,p:(st[0]>st[1])&(st[1]>st[0])^full
	_ds=lambda st,op,full,p:st[1]^[full,p.getValue(~st[0])]
	_mp=lambda st,op,full,p:st[1]^[full,p.getValue(st[0])]
	_hs=lambda st,op,full,p:[(st[0]>q.statements[1])^[full,q] for q in p.getValueMatch(lambda x:(x.statements[0]==st[1])&(x.operator==Operators.IMPLICATION))]

	HS=Rule(_hs,name="Hypothetical Syllogism")
	DS=Rule(_ds,conditions=[lambda st,p:p.getValue(~st.statements[0])],name="Disjunctive Syllogism")
	MP=Rule(_mp,conditions=[lambda st,p:p.getValue(st.statements[0])],name="Modus Ponens")
	IMPL=Rule(_impl,name="Implication")
	RIMPL=Rule(_rimpl,name="Implication")
	SYM=Rule(_sym,name="Commutativity")

class Operators:
	NOPERATOR=Operator("def","",[],syntax="{0}",truthEvaluation=(lambda args:args))
	AND=Operator("and","&",[Rules.SYM],truthEvaluation=(lambda a,b:a&b))
	OR=Operator("or","|",[Rules.SYM,Rules.DS,Rules.RIMPL],truthEvaluation=(lambda a,b:a|b))
	NOT=Operator("not","~",[],syntax="!{0}",truthEvaluation=(lambda a:True^a))
	IMPLICATION=Operator("implication",">",[Rules.HS,Rules.MP,Rules.IMPL],truthEvaluation=(lambda a,b:a<=b))
	EQUIVILANCE=Operator("equivilance","=",[Rules.SYM],truthEvaluation=(lambda a,b:a==b))

if __name__=="__main__":
	StatementParenthesis=False
	x=Inspecific.X
	y=Inspecific.Y
	b=Statement(x,"B")
	a=Statement(x,"A")
	c=Statement(x,"C")
	d=Statement(x,"D")
	conc=d
	p=Pool([a>b,b>c,c>d,a])
	p.completePool()
	hal=p.checkForConclusion(conc)
	print(p.pool)
	print("\n\n".join([str(st) for st in p.iFullPool()]))
	print(hal.parentLayers,hal,hal.parents)
	print(p.proof(conc)[-2].parents)

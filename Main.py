from functools import lru_cache

StatementParenthesis=True

_butIn=lambda l,item:[q for q in l if q!=item]
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

	def __eq__(self,other):
		if type(other)==AOperator:return(other.__eq__(self))
		return(self.name==other.name)

class AOperator(Operator):
	def __init__(self,*args,exclusion=[],**kwargs):
		super().__init__(self,*args,**kwargs)
		self.exclusion=exclusion

	def __eq__(self,other):
		if type(other)!=type(self):return(other not in self.exclusion)
		return(self.name==other.name)

class Variable:
	def __init__(self,name):
		self.name=name
	
	def __repr__(self):
		return(self.name)

class Statement:
	def __init__(self,var,name):
		self.operator=Operators.NOPERATOR
		self.variable=var
		self.name=name
		self.statements=[self]
		self._init()

	def _init(self):
		self.parents=[None]
		self.parentRule=None
		self.symetry=False
	
	@property
	def ruleParameters(self):
		return(self.statements,self.operator,self)

	@property
	def parentLayers(self):
		if self.parents==[None]:return(0)
		return(max([v.parentLayers+1 for v in self.parents]))

	def setVariable(self,newVar):
		self.variable=newVar

	lru_cache(maxsize=256)
	def returnRules(self,pool):
		return([item for lis in [v for v in [r(self,pool) for r in self.operator.rules] if v!=None] for item in _condenseIter(lis)])
	
	def __hash__(self):
		return(hash((self.name,id(self.variable))))

	def __repr__(self):
		if StatementParenthesis:
			return(f"{self.name}({self.variable})")
		return(f"{self.name}{self.variable}")
	
	def compareSym(self,other):
		return(((self.statements==other.statements)|(self.statements==other.statements[::-1]))&(other.operator==self.operator))

	def __eq__(self,other):
		if type(other)==AStatement:return(other.__eq__(self))
		if type(other)!=type(self):return(False)
		if other.symetry and not self.symetry:return(other.compareSym(self))
		if self.symetry:return(self.compareSym(other))
		if self.variable==other.variable and self.name==other.name:return(True)
		return(False)

	def __and__(self,other):
		if not isinstance(other,Statement):raise(TypeError(f"Unsupported type {type(other)}"))
		return(StatementFunc([self,other],Operators.AND))
	
	def __invert__(self):
		if self.operator==Operators.NOT:return(self.statements[0])
		return(StatementFunc(self,Operators.NOT))
	
	def __mul__(self,other):
		if not isinstance(other,Statement):raise(TypeError(f"Unsupported type {type(other)}"))
		return(StatementFunc([self,other],Operators.ABSENT))

	def __or__(self,other):
		if not isinstance(other,Statement):raise(TypeError(f"Unsupported type {type(other)}"))
		return(StatementFunc([self,other],Operators.OR))
		
	def __gt__(self,other):
		if not isinstance(other,Statement):raise(TypeError(f"Unsupported type {type(other)}"))
		return(StatementFunc([self,other],Operators.IMPLICATION))

	def __floordiv__(self,other):
		if not isinstance(other,Statement):raise(TypeError(f"Unsupported type {type(other)}"))
		return(StatementFunc([self,other],Operators.EQUIVILENCE))

	def _copy(self):
		nw=self.__new__(self.__class__)
		nw.__dict__.update(self.__dict__)
		return(nw)

	def __xor__(self,parents):
		if not hasattr(parents,"__iter__"):parents=[parents]
		nw=self._copy()
		nw.parents=parents
		return(nw)

	@property
	def sym(self):
		nw=self._copy()
		nw.symetry=True
		return(nw)

	def __mod__(self,rule):
		nw=self._copy()
		nw.parentRule=rule
		return(nw)

class AStatement(Statement):
	def __init__(self,u,o=None):
		self.ident=u
		self.o=o!=None
		self.operator=(o if self.o else None)

	def __eq__(self,other):
		if type(other)==AStatement and o:return((self.ident==other.ident)&(self.operator==other.operator))
		if type(other)==AStatement:return(self.ident==other.ident)
		return(True)

	def __hash__(self):
		return(hash((self.ident,self.operator)))

	def __repr__(self):
		return(f"{self.ident}")

class StatementFunc(Statement):
	def __init__(self,statements,operator):
		self.statements=_condenseIter(statements)
		self.operator=operator
		super()._init()
	
	def __eq__(self,other):
		if type(other)==AStatement:return(other.__eq__(self))
		if type(other)!=type(self):return(False)
		if other.symetry and not self.symetry:return(other.compareSym(self))
		if self.symetry:return(self.compareSym(other))
		if self.operator==other.operator and other.statements==self.statements:return(True)
		return(False)

	def __repr__(self):
		ret=[]
		for s in self.statements:
			if type(s)==type(self):
				if len(s.statements)>1:
					ret.append(f"({repr(s)})")
					continue
			ret.append(repr(s))
		return(self.operator.makeSyntax(ret))

	def __hash__(self):
		return(hash((self.conclusion,hash(self.statements))))

class Pool:
	def __init__(self,propositions,conclusion):
		self.conclusion=conclusion
		self.propositions=propositions
		self.pool=list(propositions)
		self.initialPool=list(propositions)
	
	def __hash__(self):
		return(hash((self.conclusion,len(self.pool))))

	def setConclusion(self,newConclusion):
		self.conclusion=newConclusion

	def append(self,newObject):
		if not (newObject in self.pool):
			self.pool.append(newObject)
		return(self)

	def addPool(self,statement):
		for st in statement.returnRules(self):
			self.append(st)

	def checkForConclusion(self):
		for ob in self.pool:
			if ob==self.conclusion:
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
	
	def getValueMatch(self,matchLambda,conc=False,er=False):
		ret=[]
		errs=[]
		for ob in [*self.pool,*([self.conclusion] if conc else [])]:
			try:
				if matchLambda(ob):
					ret.append(ob)
			except Exception as e:errs.append(e)
		if er:
			return(ret,errs)
		return(ret)

	def proof(self):
		concluded=self.checkForConclusion()
		if concluded==None:
			return(None)
		proof=list(zip([i for i in range(1,len(self.initialPool)+1)],self.initialPool,[None for i in range(len(self.initialPool))]))
		numberer=lambda x:[p[0] for p in proof if p[1] in x.parents]
		paren=lambda x:_flatten([[*paren(b),b] if b.parents!=[None] else b for b in x.parents])
		steps=[p for p in paren(concluded) if p not in self.initialPool]+[concluded]
		for n,h in enumerate(steps):
			proof.append((n+len(self.initialPool)+1,h,(numberer(h),h.parentRule)))
		return(proof)

	@property
	def contradictions(self):
		contradictions=[]
		for item in self.pool:
			if (~item in self.pool) and not ([~item,item] in contradictions):
				contradictions.append([item,~item])
		return(contradictions)

class Insp:
	X=Variable(name="x")
	Y=Variable(name="y")
	Z=Variable(name="z")
	Xs=AStatement("X")
	Ys=AStatement("Y")

class Rules:
	_impl=lambda st,op,full,p:((~st[0])|st[1])^full
	_sym=lambda st,op,full,p:StatementFunc([st[1],st[0]],op)^full
	_rimpl=lambda st,op,full,p:(~st[0]>st[1])^full
	_equiv1=lambda st,op,full,p:(st[0]>st[1])&(st[1]>st[0])^full
	_ds=lambda st,op,full,p:st[1]^[full,p.getValue(~st[0])]
	_mp=lambda st,op,full,p:st[1]^[full,p.getValue(st[0])]
	_hs=lambda st,op,full,p:[(st[0]>q.statements[1])^[full,q] for q in p.getValueMatch(lambda x:(x.statements[0]==st[1])&(x.operator==Operators.IMPLICATION))]
	_dm=lambda st,op,full,p:(~StatementFunc([~st[0],~st[1]],(Operators.AND if op==Operators.OR else Operators.OR)))^full
	_rdm=lambda st,op,full,p:(StatementFunc([~st[0].statements[0],~st[0].statements[1]],(Operators.AND if op==Operators.OR else Operators.OR)))^full
	_simp=lambda st,op,full,p:[st[0]^full,st[1]^full]
	_addOrM=lambda st,p:lambda match:((~(Insp.Xs|st).sym)|Insp.Xs) in [*match.returnRules(p),match]#ITS THE REUTRN RULES
	_addImplM=lambda st,p:lambda match:((~(Insp.Xs>st))|Insp.Xs) in [*match.returnRules(p),match]
	_addOr=lambda st,op,full,p:[((full|q)^full) for q in p.getValueMatch(Rules._addOrM(full,p))]
	_addImpl=lambda st,op,full,p:[((full|(~q))^full) for q in p.getValueMatch(Rules._addImplM(full,p))]
	_add=lambda st,op,full,p:Rules._addImpl(st,op,full,p)+Rules._addOr(st,op,full,p)
	#match if ~(a|b)|x in return rules or is object

	HS=Rule(_hs,name="Hypothetical Syllogism")
	ADD=Rule(_add,name="Addition")
	SIMP=Rule(_simp,name="Simplification")
	DM=Rule(_dm,name="De Morgan's Rule")
	RDM=Rule(_rdm,name="De Morgan's Rule")
	DS=Rule(_ds,conditions=[lambda st,p:p.getValue(~st.statements[0])],name="Disjunctive Syllogism")
	MP=Rule(_mp,conditions=[lambda st,p:p.getValue(st.statements[0])],name="Modus Ponens")
	IMPL=Rule(_impl,name="Implication")
	RIMPL=Rule(_rimpl,name="Implication")
	SYM=Rule(_sym,name="Commutativity")

class Operators:
	NOPERATOR=Operator("def","",[],syntax="{0}",truthEvaluation=(lambda args:args))
	ABSENT=AOperator("A","*",[])
	AND=Operator("and","&",[Rules.SYM,Rules.DM,Rules.SIMP,Rules.ADD],truthEvaluation=(lambda a,b:a&b))
	OR=Operator("or","|",[Rules.SYM,Rules.DS,Rules.RIMPL,Rules.DM],truthEvaluation=(lambda a,b:a|b))
	NOT=Operator("not","~",[],syntax="!{0}",truthEvaluation=(lambda a:True^a))
	IMPLICATION=Operator("implication",">",[Rules.HS,Rules.MP,Rules.IMPL],truthEvaluation=(lambda a,b:a<=b))
	EQUIVILENCE=Operator("equivalence","=",[Rules.SYM],truthEvaluation=(lambda a,b:a==b))

def _test():
	global StatementParenthesis
	StatementParenthesis=False
	x=Insp.X
	y=Insp.Y
	a=Statement(x,"A")
	b=Statement(x,"B")
	c=Statement(x,"C")
	d=Statement(x,"D")
	conc=c
	p=Pool([(~a|b)>c,a],conc)
	p.completePool()
	print(((Insp.Xs>b)>c)==(((b*a).sym)>c))
	print(Operators.ABSENT==Operators.AND)
	print(Rules._addOrM(a,p)((~(a|b))|c))
	hal=p.checkForConclusion()
	print(p.contradictions)
	print(p.pool,hal)
	if hal==None:return()
	propformat=lambda x:f"P{x[0]}) {x[1]} "+("" if x[2]==None else f"({', '.join([f'P{j}' for j in x[2][0]])} | {x[2][1].name})")
	print("\n".join(map(propformat,p.proof()))+f"\nC) {conc}")

if __name__=="__main__":
	_test()
from functools import lru_cache

class _anno(str):
	def __init__(self,name):self.name=name
	def __repr__(self):return(self.name)

StatementParenthesis=True


_condenseIter=lambda x:([x] if not hasattr(x,"__iter__") else x)
_flatten=lambda *x:[e for a in x for e in (_flatten(*a) if hasattr(a,"__iter__") else (a,))]

class Rule:
	"""Class that defines a rule for an operation by taking an input StatementObject and feeding it to a function"""
	def __init__(self,stateOut:_anno("function"),conditions:_anno("[function,]")=[],name:_anno("str")=None):
		self.stateOut=stateOut
		self.conditions=conditions
		self.name=name
		
	def __call__(self,statement:_anno("Statement"),pool:_anno("Pool"))->_anno("[Statement,]"):
		"""Returns all evaluated rule functions using the statement, operator, and the """
		for cond in self.conditions:
			if not cond(statement,pool):
				return(None)
		return([k%self for k in _condenseIter(self.stateOut(*statement.ruleParameters,pool))])

	def __repr__(self):
		return(f"Rule[{self.name}]")

class Operator:
	"""Class that contains rules used in evaluation"""
	def __init__(self,name:_anno("str"),symbols:_anno("str/[str,]"),rules:_anno("[Rule,]"),syntax:_anno("str")=None,truthEvaluation:_anno("function")=lambda a,b:True,inv=None):
		self.inv=self
		if type(inv)==Operator:self.inv=inv
		self.name=name
		if (not hasattr(symbols,"__iter__")) or type(symbols)==str:
			symbols=[symbols]
		self.symbols=symbols
		self.rules=rules
		self.syntax=f"{{0}}{symbols[0]}{{1}}"
		if syntax!=None:self.syntax=syntax
	
	def makeSyntax(self,statements:_anno("[Statement,]"))->_anno("str"):
		"""Creates a syntax using statements and a guide"""
		return(self.syntax.format(*statements))

	def __repr__(self):
		return(self.symbols[0])

	def __eq__(self,other)->_anno("bool"):
		if type(other)==AOperator:return(other.__eq__(self))
		return(self.name==other.name)

class AOperator(Operator):
	"""An operator class that is used for matching comparisons"""
	def __init__(self,*args,exclusion:_anno("[Statement,]")=[],**kwargs):
		super().__init__(self,*args,**kwargs)
		self.exclusion=exclusion

	def __eq__(self,other)->_anno("bool"):
		if type(other)!=type(self):return(other not in self.exclusion)
		return(self.name==other.name)

class Variable:
	"""A variable object used in Statements"""
	def __init__(self,name:_anno("str")):
		self.name=name
	
	def __repr__(self):
		return(self.name)

class Statement:
	"""Statement object"""
	def __init__(self,var:_anno("Variable"),name:_anno("str")):
		self.operator=Operators.NOPERATOR
		self.variable=var
		self.name=name
		self.statements=[self]
		self._init()

	def _init(self):
		"""instance wide initialisation"""
		self.parents=[None]
		self.parentRule=None
		self.symetry=False
	
	def __getitem__(self,index):
		return(self.statements[index])
	
	@property
	def ruleParameters(self):
		return(self,self.operator)

	@property
	def parentLayers(self):
		if self.parents==[None]:return(0)
		return(max([v.parentLayers+1 for v in self.parents]))

	def setVariable(self,newVar):
		self.variable=newVar

	lru_cache(maxsize=256)
	def returnRules(self,pool,but=[]):
		return([item for lis in [v for v in [r(self,pool) for r in [d for d in self.operator.rules if d not in but]] if v!=None] for item in _condenseIter(lis)])
	
	def __hash__(self):
		return(hash((self.name,id(self.variable))))

	def __repr__(self):
		return(self.name)#remove for implementation
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
	
	def cc(self,conversion,checks=[]):
		for check in checks:
			if not check(self):
				return(self)
		return(conversion(self._copy()))

class AStatement(Statement):
	def __init__(self,name,o=None):
		self.name=name
		self.statements=[self]
		self.o=o!=None
		self.operator=(o if self.o else AOperator("A","*",[]))
		self.no=[]
		self._init()

	def __eq__(self,other):
		if type(other)==AStatement and self.o:return((self.name==other.name)&(self.operator==other.operator))
		if type(other)==AStatement:return(self.name==other.name)
		return(other not in self.no)

	def __hash__(self):
		return(hash((self.name,self.operator)))

	def __repr__(self):
		return(f"{self.name}")
	
	def __lshift__(self,other):
		nw=self._copy()
		nw.no=[other]+self.no
		return(nw)

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

	def proof(self,but=[]):
		concluded=self.checkForConclusion()
		if concluded==None:
			return(None)
		proof=list(zip([i for i in range(1,len(self.initialPool)+1)],self.initialPool,[None for i in range(len(self.initialPool))]))
		if concluded.parents==[None]:
			return(proof)
		numberer=lambda x:[p[0] for p in proof if p[1] in x.parents]
		paren=lambda x:_flatten([[*paren(b),b] if b.parents!=[None] else b for b in x.parents])
		steps=[p._copy() for p in paren(concluded) if p not in self.initialPool]+[concluded]
		steps=[i for n,i in enumerate(steps) if i not in steps[:n]]
		rep=True
		while rep:
			rep=False
			for s in steps:
				if s.parentRule in but:
					steps.remove(s)
					rep=True
				for q in range(len(s.parents)):
					if s.parents[q].parentRule in but:
						s.parents+=s.parents[q].parents
						s.parents.remove(s.parents[q])
						rep=True
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
	
	def reset(self):
		self.pool=self.initialPool
	
	def toConclusion(self):
		prevpool=self.pool.copy()
		self.fullPool()
		newpool=self.pool.copy()
		if self.checkForConclusion()!=None:return()
		while prevpool!=newpool:
			prevpool=newpool
			self.fullPool()
			newpool=self.pool.copy()
			if self.checkForConclusion()!=None:return()

class Insp:
	X=Variable(name="x")
	Y=Variable(name="y")
	Z=Variable(name="z")
	Xs=AStatement("X")
	Ys=AStatement("Y")

class Rules:
	_recurse=[]
	_implConv=(lambda m:(~m[0])|m[1],[lambda m:m.operator==Operators.IMPLICATION])
	_equivConv=(lambda m:((m[0]&m[1])|((~m[0])&(~m[1]))),[lambda m:m.operator==Operators.EQUIVILENCE])
	_dmConv=(lambda m:(lambda q:StatementFunc([~(q[0]),~(q[1])],q.operator.inv))(m[0].cc(*Rules._equivConv).cc(*Rules._implConv)),[lambda m:m.operator==Operators.NOT,lambda m:len(m[0].statements)>1])
	_aoConv=lambda m:m.cc(*Rules._implConv).cc(*Rules._equivConv).cc(*Rules._dmConv)
	def _andOrConv(m):
		m=Rules._aoConv(m)
		if [m]==m.statements:
			return(m)
		return(StatementFunc([Rules._andOrConv(s) for s in m.statements],m.operator))
	_impl=lambda full,op,p:((~full[0])|full[1])^full
	_sym=lambda full,op,p:StatementFunc([full[1],full[0]],op)^full
	_rimpl=lambda full,op,p:(~full[0]>full[1])^full
	_equiv1=lambda full,op,p:(full[0]>full[1])&(full[1]>full[0])^full
	_ds=lambda full,op,p:full[1]^[full,p.getValue(~full[0])]
	_mp=lambda full,op,p:full[1]^[full,p.getValue(full[0])]
	_hs=lambda full,op,p:[(full[0]>q[1])^[full,q] for q in p.getValueMatch(lambda x:(x.statements[0]==full[1])&(x.operator==Operators.IMPLICATION))]
	_dm=lambda full,op,p:(~StatementFunc([~full[0],~full[1]],full.operator.inv))^full
	_rdm=lambda full,op,p:(StatementFunc([~full[0][0],~full[0][1]],full[0].operator.inv))^full
	_simp=lambda full,op,p:[full[0]^full,full[1]^full]
	_equiv1=lambda full,op,p:((full[0]&full[1])|(~full[0]&~full[1]))^full
	_equiv2=lambda full,op,p:((full[0]>full[1])&(full[1]>full[0]))^full
	def _add(full,op,p):
		#weird double time issue
		ret=[]
		ops=(Operators.OR,)
		compare1=(~Insp.Xs)|Insp.Xs
		compare2=(Insp.Xs*Insp.Xs)
		fm=Rules._andOrConv(full).sym
		search=lambda match:compare1==match
		found=p.getValueMatch(search)
		pruned=[Rules._andOrConv(q) for q in found]+[Rules._andOrConv(~p.conclusion)]
		foundPruned=lambda a,b:a^b if ((len(a.statements)==1)|(Rules._andOrConv(~a)==fm)) else [foundPruned(h,a) for h in a.statements]
		pruned=[foundPruned(h,h) for h in pruned]
		prunes=[Rules._andOrConv(~p)^p.parents for p in _flatten(pruned)]
		for p in prunes:
			if fm==p:
				if p.parents[0].operator.inv in ops:
					par=Rules._andOrConv(~p.parents[0])
					a,b=par.statements
					if a==fm:
						a=full
						ret.append((a|b)^full)
					else:
						b=full
						ret.append((b|a)^full)
		return(ret)
		
	def _conj(full,op,p):
		#return([])
		#integrate better time effeciency and fix bugs
		#add capture for conclusion
		ret=[]
		ops=(Operators.AND,)
		compare1=(~Insp.Xs)|Insp.Xs
		compare2=(Insp.Xs*Insp.Xs)
		fm=Rules._andOrConv(full).sym
		search=lambda match:compare1==match
		found=p.getValueMatch(search)
		pruned=[Rules._andOrConv(q) for q in found]+[Rules._andOrConv(~p.conclusion)]
		foundPruned=lambda a,b:a^b if ((len(a.statements)==1)|(Rules._andOrConv(~a)==fm)) else [foundPruned(h,a) for h in a.statements]
		pruned=[foundPruned(h,h) for h in pruned]
		prunes=[Rules._andOrConv(~p)^p.parents for p in _flatten(pruned)]
		for pr in prunes:
			if fm==pr:
				if pr.parents[0].operator.inv in ops:
					par=Rules._andOrConv(~pr.parents[0])
					a,b=par.statements
					if a==fm:
						a=full
						if b==p.getValue(b):
							b=p.getValue(b)
							ret.append((a&b)^[full,b])
					else:
						b=full
						if a==p.getValue(a):
							a=p.getValue(a)
							ret.append((b&a)^[full,a])
		return(ret)

	ADD=Rule(_add,name="Addition")
	CONJ=Rule(_conj,name="Conjunction")
	_recurse.append(ADD)
	_recurse.append(CONJ)
	HS=Rule(_hs,name="Hypothetical Syllogism")
	SIMP=Rule(_simp,name="Simplification")
	DM=Rule(_dm,name="De Morgan's Rule")
	RDM=Rule(_rdm,name="De Morgan's Rule",conditions=[lambda st,p:len(st[0].statements)>1])
	DS=Rule(_ds,conditions=[lambda st,p:p.getValue(~(st[0]))],name="Disjunctive Syllogism")
	MP=Rule(_mp,conditions=[lambda st,p:p.getValue(st[0])],name="Modus Ponens")
	IMPL=Rule(_impl,name="Implication")
	RIMPL=Rule(_rimpl,name="Implication")
	SYM=Rule(_sym,name="Commutativity")

class Operators:
	NOPERATOR=Operator("def","",[Rules.ADD,Rules.CONJ],syntax="{0}",truthEvaluation=(lambda args:args))
	ABSENT=AOperator("A","*",[])
	AND=Operator("and","∧",[Rules.ADD,Rules.SYM,Rules.DM,Rules.SIMP,Rules.ADD,Rules.CONJ],truthEvaluation=(lambda a,b:a&b))
	OR=Operator("or","∨",[Rules.ADD,Rules.SYM,Rules.DS,Rules.RIMPL,Rules.DM,Rules.CONJ],truthEvaluation=(lambda a,b:a|b),inv=AND)
	AND.inv=OR
	NOT=Operator("not","¬",[Rules.ADD,Rules.CONJ,Rules.RDM],syntax="¬{0}",truthEvaluation=(lambda a:True^a))
	IMPLICATION=Operator("implication","→",[Rules.ADD,Rules.HS,Rules.MP,Rules.IMPL,Rules.CONJ],truthEvaluation=(lambda a,b:a<=b))
	EQUIVILENCE=Operator("equivalence","≡",[Rules.ADD,Rules.SYM,Rules.CONJ],truthEvaluation=(lambda a,b:a==b))

def _test():
	global StatementParenthesis
	StatementParenthesis=False
	x=Insp.X
	y=Insp.Y
	p=Statement(x,"p")
	q=Statement(x,"q")
	r=Statement(x,"r")
	s=Statement(x,"s")
	t=Statement(x,"t")
	conc=~(s|t)
	p=Pool([
		(~p|q)>(~(r&s)),
		(r&p)>t,
		r&(~t)
		],conc)
	p.toConclusion()
	hal=p.checkForConclusion()
	print("conclusion:",hal)
	print("contradictions:",p.contradictions)
	if hal==None:return()
	print("proof:")
	propformat=lambda x:f"P{x[0]}) {x[1]} "+("" if x[2]==None else f"({', '.join([f'P{j}' for j in x[2][0]])} | {x[2][1].name})")
	print("\n".join(map(propformat,p.proof(but=[Rules.SYM])))+f"\nC) {conc}")

if __name__=="__main__":
	import timeit
	print("Time (ms):",int(timeit.timeit(_test,number=1)*1e+7)/1e+4)

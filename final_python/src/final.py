from prolog_structures import Rule, RuleBody, Term, Function, Variable, Atom, Number
from typing import List
from functools import reduce

import sys
import random

class Not_unifiable(Exception):
	pass

'''
Please read prolog_structures.py for data structures
that represent Prolog terms, rules, and goals.
'''
class Interpreter:
	def __init__(self):
		pass

	'''
	Example
	occurs_check (v, t) where v is of type Variable, t is of type Term.
	occurs_check (v, t) returns true if the Prolog Variable v occurs in t.
	Please see the lecture note Control in Prolog to revisit the concept of
	occurs-check.
	'''
	def occurs_check (self, v : Variable, t : Term) -> bool:
		if isinstance(t, Variable):
			return v == t
		elif isinstance(t, Function):
			for t in t.terms:
				if self.occurs_check(v, t):
					return True
			return False
		return False


	'''
	Problem 1
	variables_of_term (t) where t is of type Term.
	variables_of_clause (c) where c is of type Rule.

	The function should return the Variables contained in a term or a rule
	using Python set.

	The result must be saved in a Python set. The type of each element (a Prolog Variable)
	in the set is Variable.
	'''
	def variables_of_term (self, t : Term) -> set :
		terms = set()
		for x in t.terms:
			if isinstance(x, Variable):
				terms.add(x)
		return terms

	def variables_of_clause (self, c : Rule) -> set :
		rules = set()
		for x in c.head.terms:
			if isinstance(x, Variable):
				rules.add(x)
		return rules


	'''
	Problem 2
	substitute_in_term (s, t) where s is of type dictionary and t is of type Term
	substitute_in_clause (s, t) where s is of type dictionary and c is of type Rule,

	The value of type dict should be a Python dictionary whose keys are of type Variable
	and values are of type Term. It is a map from variables to terms.

	The function should return t_ obtained by applying substitution s to t.

	Please use Python dictionary to represent a subsititution map.

	'''
	def substitute_in_term (self, s : dict, t : Term) -> Term:
		new_terms = []
		for count, x in enumerate(t.terms):
			if isinstance(x, Function):
				new_terms.append (self.substitute_in_term(s, x))
			else:
				new_terms.append(s.get(x,x))
		return Function(t.relation, new_terms)

	def substitute_in_clause (self, s : dict, c : Rule) -> Rule:
		newRule = c
		for count, x in enumerate(newRule.head.terms):
			if isinstance((newRule.head.terms[count]), Function):
				newRule.head.terms[count] = self.substitute_in_term(s, newRule.head.terms[count])
			else:
				newRule.head.terms[count] = s.get(x,x)
		for count, x in enumerate(newRule.body.terms):
			newRule.body.terms[count] = self.substitute_in_term(s, x)
		return Rule(newRule.head, newRule.body)

	'''
	Problem 3
	unify (t1, t2) where t1 is of type term and t2 is of type Term.
	The function should return a substitution map of type dict,
	which is a unifier of the given terms. You may find the pseudocode
	of unify in the lecture note Control in Prolog useful.

	The function should raise the exception raise Not_unfifiable (),
	if the given terms are not unifiable.

	Please use Python dictionary to represent a subsititution map.
	'''
	def unify(self, t1: Term, t2:Term) -> dict:
		return self.unify2(t1, t2, dict({}))

	def unify2 (self, t1: Term, t2: Term, t3: dict) -> dict:
		s = t3
		if (len(s)==0):
			j1 = t1
			j2 = t2
		else:
			if isinstance(t1, Function):
				j1 = t1
			elif t1 in s: 
				j1 = s[t1]
			else:
				j1 = t1

			
			if isinstance(t2, Function):
				j2 = t2
			elif t2 in s: 
				j2 = s[t2]
			else: 
				j2 = t2

		if (isinstance(j1, Variable) and (self.occurs_check(j1, j2) == False)):
			for key, value in s.items():
				if value == j1: s[key] = j2
			
			s[j1] = j2
			return s
		elif (isinstance(j2, Variable) and ((self.occurs_check(j2, j1)) == False)):
			for key, value in s.items():
				if value == j2: s[key] = j1
			
			s[j2] = j1
			return s
		elif ( isinstance(j1, Variable) and isinstance(j2, Variable) ) or ( isinstance(j2, Atom) and isinstance(j1, Atom) ) or ( isinstance(j1, Number) and isinstance(j2, Number) ):
			if j1 == j2:
				return s
			else: 
				raise Not_unifiable
		elif isinstance(j1, Function) and isinstance(j2, Function):
			if j1.relation != j2.relation or len(j1.terms) != len(j2.terms):
				raise Not_unifiable

			for j in range(len(j2.terms)):
				s.update(self.unify2(j1.terms[j], j2.terms[j], s))	
		else:
			raise Not_unifiable

		return s


	fresh_counter = 0
	def fresh(self) -> Variable:
		self.fresh_counter += 1
		return Variable("_G" + str(self.fresh_counter))
	def freshen(self, c: Rule) -> Rule:
		c_vars = self.variables_of_clause(c)
		theta = {}
		for c_var in c_vars:
			theta[c_var] = self.fresh()

		return self.substitute_in_clause(theta, c)

	'''
	Problem 4
	Following the Abstract interpreter pseudocode in the lecture note Control in Prolog to implement
	a nondeterministic Prolog interpreter.

	nondet_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of Terms (results), which is an instance of the original goal and is
	a logical consequence of the program. See the tests cases (in src/main.py) as examples.
				
	'''
	def nondet_query (self, program : List[Rule], pgoal : List[Term]) -> List[Term]:
		resolvent = pgoal.copy()
		while len(resolvent)>0:
			aGoal = resolvent[random.randint(0,len(resolvent)-1)]
			for x in program:
				aRule = self.freshen(x)

				try:
					unifier = self.unify(aGoal, aRule.head)
					break
				except: pass
			
			try: unifier
			except: break

			resolvent.remove(aGoal)
			for x in aRule.body.terms:
				resolvent.append(x)
			for x in range(len(resolvent)):
				resolvent[x] = self.substitute_in_term (unifier, resolvent[x])
			for x in range(len(pgoal)): 
				pgoal[x] = self.substitute_in_term(unifier, pgoal[x])

		return pgoal
		
		
	'''
	Challenge Problem

	det_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of term lists (results). Each of these results is
	an instance of the original goal and is a logical consequence of the program.
	If the given goal is not a logical consequence of the program, then the result
	is an empty list. See the test cases (in src/main.py) as examples.
	'''
	def dfs(self, resolvent, goal, solutions):
		if len(resolvent)==0:
			solutions.append(goal)
			return 

		while resolvent:
			chosen_goal = goal[random.randint(0, len(goal)-1)]

			for rule in resolvent:				
				try:
					test = self.unify(chosen_goal, rule.head)
				except: break

				chosen_rule = self.freshen(rule)
				unifier = self.unify(chosen_goal, chosen_rule)

				new_resolvent = resolvent.copy()
				new_goal = goal.copy()

				resolvent.remove(chosen_goal)
				for term in chosen_rule.body.terms:
					resolvent.apppend(term)
				
				for term in new_resolvent:
					new_resolvent[term] = self.substitute_in_term(unifier, term)
				
				for term in new_goal:
					new_goal[term] = self.substitute_in_term(unifier, term)

				self.dfs(new_resolvent, new_goal, solutions)
			return

	def det_query (self, program : List[Rule], pgoal : List[Term]) -> List[Term]:
		solutions = []
		self.dfs(program, pgoal, solutions)
		return solutions
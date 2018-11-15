import sys
from os import mkdir
from os.path import exists, dirname, basename, join, split
from textx.metamodel import metamodel_from_file
from textx.model import get_children_of_type
from textx.exceptions import TextXSemanticError
from textx.scoping import providers
from copy import copy, deepcopy

this_folder = dirname(__file__)

# set of actions used in the model
actions = set([])

# Classes for SLCO statements
class Assignment(object):
	def __init__(self, parent, left, right):
		self.parent = parent
		self.left = left
		self.right = right

class Composite(object):
	def __init__(self, parent, guard, assignments):
		self.parent = parent
		self.guard = guard
		self.assignments = assignments

class Expression(object):
	def __init__(self, parent, left, op, right):
		self.parent = parent
		self.left = left
		self.op = op
		self.right = right

class ExprPrec1(object):
	def __init__(self, parent, left, op, right):
		self.parent = parent
		self.left = left
		self.op = op
		self.right = right

class ExprPrec2(object):
	def __init__(self, parent, left, op, right):
		self.parent = parent
		self.left = left
		self.op = op
		self.right = right

class ExprPrec3(object):
	def __init__(self, parent, left, op, right):
		self.parent = parent
		self.left = left
		self.op = op
		self.right = right

class ExprPrec4(object):
	def __init__(self, parent, left, op, right):
		self.parent = parent
		self.left = left
		self.op = op
		self.right = right

class Primary(object):
	def __init__(self, parent, sign, value, body, ref):
		self.parent = parent
		self.sign = sign
		self.value = value
		self.body = body
		self.ref = ref

class ExpressionRef(object):
	def __init__(self, parent, ref, index):
		self.parent = parent
		self.ref = ref
		self.index = index

class Variable(object):
	def __init__(self, parent, type, name, defvalue, defvalues):
		self.parent = parent
		self.type = type
		self.name = name
		self.defvalue = defvalue
		self.defvalues = defvalues

class VariableRef(object):
	def __init__(self, parent, var, index):
		self.parent = parent
		self.var = var
		self.index = index

class Type(object):
	def __init__(self, parent, base, size):
		self.parent = parent
		self.base = base
		self.size = size

class Action(object):
	def __init__(self, parent, name):
		self.parent = parent
		self.name = name

# extra class to identify references to Actions
class ActionRef(object):
	def __init__(self, parent, act):
		self.parent = parent
		self.act = act

# extra classes for AL-SLCO models
class AL_Assignment(object):
	def __init__(self, parent, left, right):
		self.parent = parent
		self.left = left
		self.right = right
		self.cached = cached

class AL_Expression(object):
	def __init__(self, parent, left, op, right):
		self.parent = parent
		self.left = left
		self.op = op
		self.right = right
		self.cached = cached

class AL_ReadInstruction(object):
	def __init__(self, parent, ref):
		self.parent = parent
		self.ref = ref

class WriteInstruction(object):
	def __init__(self, parent, ref):
		self.parent = parent
		self.ref = ref

# method to raise semantic error
def raise_semantic_error(S, s, model):
	"""S is error message string.
	s is object in which error occurs."""
	line, col = model._tx_parser.pos_to_linecol(s._tx_position)
	S += ' at ("%s", "%s")' % (line, col)
	raise TextXSemanticError(S)

# FUNCTIONS TO CREATE INSTANCES OF SLCO CONCEPTS

def create_smlocal_var(sm, v, type, size):
	"""Create and return a variable object for the variable named v of given type and size, associated to the given state machine sm"""
	newv = Variable(sm, '', v, None, [])
	if type == "Boolean":
		t = Type(newv, 'Boolean', size)
	elif type == "Byte":
		t = Type(newv, 'Byte', size)
	else:
		t = Type(newv, 'Boolean', size)
	newv.type = t
	# add variable to list of state machine-local variables
	sm.variables.append(newv)
	return newv

def create_var_expression(st, v, i):
	"""Create and return a new expression containing only a reference to the given variable name (with possibly index i). Associate the expression with the given statement st"""
	e = Expression(st, '', '', '')
	e4 = ExprPrec4(e, '', '', '')
	e3 = ExprPrec3(e4, '', '', '')
	e2 = ExprPrec2(e3, '', '', '')
	e1 = ExprPrec1(e2, '', '', '')
	p = Primary(e1, '', '', '', '')
	r = ExpressionRef(p, v, i)
	e.left = e4
	e4.left = e3
	e3.left = e2
	e2.left = e1
	e1.left = p
	p.ref = r
	return e

# *** MODEL PROCESSORS ***

# model processor to create the set of actions
def construct_action_set(model, metamodel):
	global actions
	# construct the set of actions as they appear in the model
	actions = set([])
	for a in model.actions:
		actions.add(a.name)

# model processor to check for name clashes and remove duplicates in lists
# invalid name clashes:
# - action names cannot be used for variable names
# - classes need to have unique names
# - objects need to have unique names
def check_names(model, metamodel):
	# actions
	actlist = []
	actset = set([])
	for a in model.actions:
		if a.name not in actset:
			actset.add(a.name)
			actlist.append(a)
	model.actions = actlist

	# classes
	cnames = set([])
	for c in model.classes:
		if c.name in cnames:
			error = 'Name clash: "%s" used for multiple classes, once' % name
			raise_semantic_error(error, c, model)
		else:
			cnames.add(c.name)

	# check inside each class for variable names
	for c in model.classes:
		# variables
		varlist = []
		varset = set([])
		for v in c.variables:
			if v.name in actset:
				error = 'Name clash: "%s" used for both a variable and an action ' % name
				raise_semantic_error(error, v, model)
			else:
				if v.name not in varset:
					varset.add(v.name)
					varlist.append(v)
		c.variables = varlist
		# ports
		portlist = []
		tmp = set([])
		for p in c.ports:
			if p.name not in tmp:
				tmp.add(p.name)
				portlist.append(p)
		c.ports = portlist
		# state machines
		for sm in c.statemachines:
			varlist = []
			varset = set([])
			for v in sm.variables:
				if v.name in actset:
					error = 'Name clash: "%s" used for both a variable and an action at' % name
					raise_semantic_error(error, v, model)
				else:
					if v.name not in varset:
						varset.add(v.name)
						varlist.append(v)
			sm.variables = varlist
			# states
			statelist = []
			stateset = set([sm.initialstate.name])
			for s in sm.states:
				if s.name not in stateset:
					stateset.add(s.name)
					statelist.append(s)
			sm.states = statelist

	onames = set([])
	for o in model.objects:
		if o.name in cnames:
			error = 'Name clash: "%s" used for multiple objects, once' % o.name
			raise_semantic_error(error, o, model)
		else:
			onames.add(o.name)

# model processor adding initial state to list of states
def add_initial_to_states(model, metamodel):
	for c in model.classes:
		for stm in c.statemachines:
			stm.states = [stm.initialstate] + stm.states

# model processor filling in types of variables
def add_variable_types(model, metamodel):
	for c in model.classes:
		for i in range(0,len(c.variables)):
			if c.variables[i].type == None:
				c.variables[i].type = c.variables[i-1].type
		for sm in c.statemachines:
			for i in range(0,len(sm.variables)):
				if sm.variables[i].type == None:
					sm.variables[i].type = sm.variables[i-1].type

# model processor setting sizes of channels by default to one
def set_default_channel_size(model, metamodel):
	for ch in model.channels:
		if ch.size == 0:
			ch.size = 1

# model processor adding tau action to transitions without statements
def add_taus(model, metamodel):
	tau_needed = False
	for c in model.classes:
		for stm in c.statemachines:
			for trn in stm.transitions:
				if len(trn.statements) == 0:
					tau_needed = True
					break
			if tau_needed:
				break
		if tau_needed:
			break
	if tau_needed:
		# add tau to list of actions
		ta = Action(model, "tau")
		model.actions.append(ta)
		# add reference to tau action to all transitions without statements
		for c in model.classes:
			for stm in c.statemachines:
				for trn in stm.transitions:
					if len(trn.statements) == 0:
						trn.statements.append(ActionRef(trn, ta))

# model processor to fix and check references
def fix_references(model, metamodel):
	for c in model.classes:
		Vc = {}
		for v in c.variables:
			Vc[v.name] = v
		for sm in c.statemachines:
			V = copy(Vc)
			for v in sm.variables:
				V[v.name] = v
			statedict = {sm.initialstate.name: sm.initialstate}
			for s in sm.states:
				statedict[s.name] = s
			for tr in sm.transitions:
				# check state references of transitions
				sref = statedict.get(tr.source.name)
				if sref == None:
					error = 'Source state "%s" mentioned in transition is not defined in state machine' % tr.source.name
					raise_semantic_error(error, tr, model)
				else:
					tr.source = sref
				sref = statedict.get(tr.target.name)
				if sref == None:
					error = 'Target state "%s" mentioned in transition is not defined in state machine' % tr.target.name
					raise_semantic_error(error, tr, model)
				else:
					tr.target = sref
				# check references to actions and variables in statements
				for st in tr.statements:
					statement_check_refs(st, V, model)

def statement_check_refs(s, V, model):
	"""Auxiliary function used to check references in statements.
	V is a dictionary of references to variables in the current scope."""
	global actions

	if s.__class__.__name__ == "Assignment":
		statement_check_refs(s.left, V, model)
		statement_check_refs(s.right, V, model)
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			statement_check_refs(s.guard, V, model)
		for a in s.assignments:
			statement_check_refs(a, V, model)
	elif s.__class__.__name__ == "ReceiveSignal":
		for p in s.params:
			statement_check_refs(p, V, model)
		if s.guard != None:
			statement_check_refs(s.guard, V, model)
	elif s.__class__.__name__ == "SendSignal":
		for p in s.params:
			statement_check_refs(p, V, model)
	elif s.__class__.__name__ == "VariableRef":
		vref = V.get(s.var.name)
		if vref == None:
			error = 'There is a reference to a variable "%s" that does not exist in that scope' % s.var.name
			raise_semantic_error(error, s, model)
		else:
			# possibly fix reference to take scope into account
			s.var = vref
			# if variable is of Array type, an index must be provided
			if vref.type.size > 1 and s.index == None:
				error = 'There is a reference to an Array variable "%s" where an index is mandatory, but missing,' % s.var.name
				raise_semantic_error(error, s, model)
	elif s.__class__.__name__ != "Primary":
		statement_check_refs(s.left, V, model)
		if s.op != '':
			statement_check_refs(s.right, V, model)
	else:
		if s.ref != None:
			if s.ref.ref not in actions:
				vref = V.get(s.ref.ref)
				if vref == None:
					error = 'There is a reference to a variable "%s" that does not exist in that scope' % s.ref.ref
					raise_semantic_error(error, s, model)
				else:
					# if variable is of Array type, an index must be provided
					if vref.type.size > 1 and s.ref.index == None:
						error = 'There is a reference to an Array variable "%s" where an index is mandatory, but missing,' % s.var.name
						raise_semantic_error(error, s, model)

# model processor to simplify action references
#def simplify_statements(model, metamodel):
#	for c in model.classes:
#		for sm in c.statemachines:
#			for tr in sm.transitions:
#				for st in tr.statements:
#					if expression_is_actionref(st):
						# replace with a single class of type ActionRef
						# TODO

def expression_is_actionref(s):
	"""Determine whether the given expression is an action reference"""
	global actions
	if s.__class__.__name__ == "Expression":
		if s.op == '':
			snext = s.left
			if snext.op == '':
				snext = snext.left
				if snext.op == '':
					snext = snext.left
					if snext.op == '':
						snext = snext.left
						if snext.op == '':
							snext = snext.left
							if snext.ref != None and snext.sign == '':
								snext = snext.ref
								if snext.ref in actions:
									return True
	return False

def read_SLCO_model(m):
	"""Read, post process, and type check an SLCO model"""

	# create meta-model
	slco_mm = metamodel_from_file(join(this_folder,'../textx_grammars/slco2.tx'), autokwd=True, classes=[Assignment, Composite, Expression, ExprPrec1, ExprPrec2, ExprPrec3, ExprPrec4, Primary, ExpressionRef, Variable, VariableRef, Type, Action])

	# register processors
	slco_mm.register_model_processor(construct_action_set)
	slco_mm.register_model_processor(check_names)
	slco_mm.register_model_processor(add_initial_to_states)
	slco_mm.register_model_processor(add_variable_types)
	slco_mm.register_model_processor(set_default_channel_size)
	slco_mm.register_model_processor(add_taus)
	slco_mm.register_model_processor(fix_references)
	#slco_mm.register_model_processor(simplify_statements)

# To do: Check receive statements for not receiving multiple values in the same variable

	slco_mm.register_scope_providers({
		"*.*": providers.FQN(),
		"Initialisation.left": providers.RelativeName("parent.type.variables"),
		"Channel.ports[0]": providers.RelativeName("source.type.ports"),
		"Channel.ports[1]": providers.RelativeName("target.type.ports"),
		"ReceiveSignal.from": providers.RelativeName("parent.parent.parent.type.ports"),
		"SendSignal.to": providers.RelativeName("parent.parent.parent.type.ports")
	})

	# parse and return the model
	return slco_mm.model_from_file(m)

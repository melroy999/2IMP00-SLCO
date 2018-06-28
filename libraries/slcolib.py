import sys
from os import mkdir
from os.path import exists, dirname, basename, join, split
from textx.metamodel import metamodel_from_file
from copy import deepcopy

this_folder = dirname(__file__)

# Classes for SLCO statements
class Assignment(object):
	def __init__(self, parent, left, right):
		self.parent = parent
		self.left = left
		self.right = right

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

class Type(object):
	def __init__(self, parent, base, size):
		self.parent = parent
		self.base = base
		self.size = size

def preprocess():
	"""preprocessing method"""
	global model, porttypes, scopedvars, smlocalvars, signaltypes, states, channeltypes, asynclosslesstypes, asynclossytypes, synctypes, actions, visibleactions, syncactionlabelsdict, classobjects, class_receives, statemachine, tr, check_rc, modelvars, statemachinenames

	# build map between synchronisation actions. also record whether the synchronisation is 'direct' (between objects) or indirect 'via channels'
	for c in model.channels:
		if c.synctype == 'async':
			syncactionlabelsdict[sendactionlabel(c)] = tuple([tuple(["insert_", c.source.name + "'" + c.ports[0].name, c.source]), commsendactionlabel(c), False])
			syncactionlabelsdict[receiveactionlabel(c)] = tuple([tuple(["remove_", c.target.name + "'" + c.ports[1].name, c.target]), commreceiveactionlabel(c), False])
			syncactionlabelsdict[peekactionlabel(c)] = tuple([tuple(["show_", c.target.name + "'" + c.ports[1].name, c.target]), commpeekactionlabel(c), False])
		else:
			syncactionlabelsdict[sendactionlabel(c)] = tuple([tuple([mcrl2objectreceive + "_", c.target.name + "'" + c.ports[1].name, c.target]), syncactionlabel(c), True])
			syncactionlabelsdict[receiveactionlabel(c)] = tuple([tuple([mcrl2objectsend + "_", c.source.name + "'" + c.ports[0].name, c.source]), syncactionlabel(c), True])
			syncactionlabelsdict[sendpeekactionlabel(c)] = tuple([tuple([mcrl2objectpeek + "_", c.target.name + "'" + c.ports[1].name, c.target]), peeksyncactionlabel(c), True])
			syncactionlabelsdict[peekactionlabel(c)] = tuple([tuple(["show_", c.source.name + "'" + c.ports[0].name, c.source]), peeksyncactionlabel(c), True])

	# create a list of statements representing receives for each class
	class_receives = {}
	for c in model.classes:
		slist = []
		for stm in c.statemachines:
			for trn in stm.transitions:
				for stat in trn.statements:
					if stat.__class__.__name__ == "ReceiveSignal":
						slist.append(stat)
		# record list
		class_receives[c] = slist
	# construct a dictionary of visible actions per class
	visibleactions = {}
	# temporary dict to ensure that no two statements are stored in visibleactions with the same label
	visibleactionstrings = {}
	if not check_rc:
		for c in model.classes:
			for stm in c.statemachines:
				for trn in stm.transitions:
					for stat in trn.statements:
						if expression_is_actionref(stat):
							stringset = visibleactionstrings.get(c, set([]))
							if statementactionlabel(stat,c,False) not in stringset:
								stringset.add(statementactionlabel(stat,c,False))
								visibleactionstrings[c] = stringset
								actset = visibleactions.get(c, set([]))
								actset.add(stat)
								visibleactions[c] = actset
	# add other visible actions, in case of race condition checking
	else:
		for c in model.classes:
			for stm in c.statemachines:
				for trn in stm.transitions:
					for stat in trn.statements:
						if stat.__class__.__name__ == "Assignment" or stat.__class__.__name__ == "Composite" or (stat.__class__.__name__ == "Expression" and not expression_is_actionref(stat)):
							stringset = visibleactionstrings.get(c, set([]))
							if statementactionlabel(stat,c,False) not in stringset:
								stringset.add(statementactionlabel(stat,c,False))
								visibleactionstrings[c] = stringset
								actset = visibleactions.get(c, set([]))
								actset.add(stat)
								visibleactions[c] = actset

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

# model processor adding tau actions to transitions without statements
def add_taus(model, metamodel):
	for c in model.classes:
		for stm in c.statemachines:
			for trn in stm.transitions:
				if len(trn.statements) == 0:
					trn.statements.append("tau'")

# model processor fixing wrong references from transitions to states (scope errors)
# raises an error if the state does not exist
def fix_state_refs(model, metamodel):
	for c in model.classes:
		for sm in c.statemachines:
			sdict = {}
			for s in sm.states:
				sdict[s.name] = s
			for tr in sm.transitions:
				name = sdict.get(tr.source.name)
				if name == None:
					raise TextXSemanticError('Source state "%s" mentioned in transition is not defined in state machine.' % tr.source.name)
				elif tr.source != name:
					tr.source = sdict[tr.source.name]
				name = sdict.get(tr.target.name)
				if name == None:
					raise TextXSemanticError('Target state "%s" mentioned in transition is not defined in state machine.' % tr.target.name)
				elif tr.target != name:
					tr.target = sdict[tr.target.name]

# model processor giving transitions without a priority a high enough priority value, such that they actually get the lowest priority
	prios = {}
	for c in model.classes:
		for stm in c.statemachines:
			prios = {}
			for trn in stm.transitions:
				if prios.get(trn.source.name,0) == 0:
					prios[trn.source.name] = trn.priority
				else:
					if trn.priority > prios[trn.source.name]:
						prios[trn.source.name] = trn.priority
			# assign new priorities
			for trn in stm.transitions:
				if trn.priority == 0:
					trn.priority = prios[trn.source.name]+1


def read_SLCO_model(m):
	"""Read, post-process, and type-check an SLCO model"""
	global model

	# create meta-model
	slco_mm = metamodel_from_file(join(this_folder,'../textx_grammars/slco2.tx'), classes=[Assignment, Expression, ExprPrec1, ExprPrec2, ExprPrec3, ExprPrec4, Primary, ExpressionRef, Variable, Type])

	# register processors
	slco_mm.register_model_processor(add_initial_to_states)
	slco_mm.register_model_processor(add_variable_types)

	# parse and return the model
	return slco_mm.model_from_file(m)

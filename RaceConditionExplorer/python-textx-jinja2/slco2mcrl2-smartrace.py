import sys
from os import mkdir
from os.path import exists, dirname, basename, join, split
import jinja2
from textx.metamodel import metamodel_from_file
from copy import deepcopy
import itertools
import glob
import traceback
from SCCTarjan import identifySCCs

# on-the-fly race condition checking
check_onthefly = False
# lock on-the-fly
lock_onthefly = False
# apply por
apply_por = False

modelname = ""
model = ""
this_folder = dirname(__file__)
# type of ports
porttypes = {}
# statemachine names used in the model
statemachinenames = set([])
# set of state names used in the model
states = set([])
# set of actions used in the model
actions = set([])
# dictionary to look up state machine owning a given statement
statemachine = {}
# dictionary to look up class owning a given state machine
smclass = {}
# dictionary to look up transition owning a given statement
trowner = {}
# dictionary providing the type of all model variables (with class-based scopes)
vartypes = {}
# per class / statemachine, give a dictionary, making the scope of variables explicit
scopedvars = {}
# per class / statemachine, give a set of local variables
smlocalvars = {}
# transitions of state machines stored in dictionary per class/state machine/source state
trans = {}
# the summands for the output mCRL2 model
mcrl2summands = []

mcrl2varprefix = "var_"

# the type of the involved channels
channeltypes = {}
asynclosslesstypes = set([])
asynclossytypes = set([])
synctypes = set([])

# partitioning of the statements into safe and unsafe statements
unsafe_statements = set([])
safe_statements = set([])

# unsafe variables are those referenced in unsafe statements
unsafe_variables = []

# dictionary to look up channel linked to a given (object) statement
ochannel = {}
# set of pairs of communicating objects
object_sync_commpairs = set([])

# dictionary providing the access patterns of statements
statement_access = {}
statement_condition_access = {}

# statements that require syncing
syncing_statements = {}

# sorted list of variables in the model
sorted_variables = []

def RepresentsInt(s):
    try: 
        int(s)
        return True
    except ValueError:
        return False

def hascondition(s, o):
	"""Returns if the given statement has a condition. o is the Object owning s."""
	global ochannel
	if s.__class__.__name__ == "Expression":
		return not expression_is_actionref(s)
	elif s.__class__.__name__ == "SendSignal":
		return ochannel[o][s].synctype == "async"
	elif s.__class__.__name__ == "ReceiveSignal":
		if s.guard != None:
			return True
		else:
			return ochannel[o][s].synctype == "async"
	elif s.__class__.__name__ == "Composite":
		return s.guard != None
	return False

def variabledefault(s):
	""" return default value for given variable """
	if s.defvalue != None:
		return s.defvalue
	elif s.defvalues != []:
		defv = '['
		first = True
		for v in s.defvalues:
			if not first:
				defv += ','
			else:
				first = False
			defv += str(v)
		defv += ']'
		return defv
	elif s.type.base == 'Integer' or s.type.base == 'Byte':
		if s.type.size < 2:
			return '0'
		else:
			type = '['
			first = True
			for i in range(0,s.type.size):
				if not first:
					type += ','
				else:
					first = False
				type += '0'
			type += ']'
			return type
	elif s.type.base == 'Boolean':
		if s.type.size < 2:
			return 'true'
		else:
			type = '['
			first = True
			for i in range(0,s.type.size):
				if not first:
					type += ','
				else:
					first = False
				type += 'true'
			type += ']'
			return type

def hasobjectvariables(m):
	""" Filter to check whether the given model have object variables"""
	found = False
	for c in m.classes:
		if len(c.variables) > 0:
			found = True
			break
	return found

def hasvariables(o):
	""" Test to check whether given object has object variables"""
	return len(o.type.variables) > 0

def hasindex(v):
	""" Test to check whether given (variable / variable scope name) pair has an index"""
	return v[0].type.size > 1

def hasnoindex(v):
	""" Test to check whether given (variable / variable scope name) pair has no index"""
	return v[0].type.size <= 1

def datatypeacronym(s):
	""" return acronym for given data type """
	if s == 'Int':
		return 'I'
	elif s == 'Bool':
		return 'B'
	elif s == 'List(Int)':
		return 'LI'
	elif s == 'List(Bool)':
		return 'LB'

def mcrl2type(s):
	"""Maps type names from SLCO to mCRL2"""
	if s.base == 'Integer' or s.base == 'Byte':
		if s.size < 2:
			return 'Int'
		else:
			return 'List(Int)'
	elif s.base == 'Boolean':
		if s.size < 2:
			return 'Bool'
		else:
			return 'List(Bool)'

def mcrl2value(s):
	"""Maps values from SLCO to mCRL2 values"""
	return str(s).lower()

def mcrl2typetuple(s):
	"""Maps list of type names from SLCO to mCRL2"""
	newtype = []
	for t in s:
		newtype.append(mcrl2type(t))
	return tuple(newtype)

def operator(s):
	"""Maps SLCO expression operators to mCRL2 operators"""
	if s == '=':
		return '=='
	elif s == '<>':
		return '!='
	elif s == '<=':
		return '<='
	elif s == '>=':
		return '>='
	elif s == '<':
		return '<'
	elif s == '>':
		return '>'
	elif s == '+':
		return '+'
	elif s == '-':
		return '-'
	elif s == 'or':
		return '||'
	elif s == 'xor':
		return 'xor'
	elif s == 'and':
		return '&&'
	elif s == '*':
		return '*'
	elif s == '/':
		return '/'
	elif s == '%':
		return 'mod'
	elif s == '**':
		return 'exp'
	elif s == 'not':
		return '!'
	return ''

def mcrl2_model_vartypes(m, startsep):
	"""Return a string containing the types of the variables in the given model, mCRL2 style.
	startsep indicates whether we should start with a separator or not"""
	result = ""
	first = True
	for o in model.objects:
		for v in o.type.variables:
			if not first or startsep:
				result += " # "
			else:
				first = False
			result += mcrl2type(v.type)
		for sm in o.type.statemachines:
			for v in sm.variables:
				if not first or startsep:
					result += " # "
				else:
					first = False
				result += mcrl2type(v.type)
	for ch in model.channels:
		if ch.synctype == 'async':
			if not first or startsep:
				result += " # "
			else:
				first = False
			result += "List(M'"
			for t in mcrl2typetuple(ch.type):
				result += datatypeacronym(t)
			result += ") # Int"
	return result

def mcrl2_model_vars(m, startsep):
	"""Return a string containing the names of the variables in the given model, mCRL2 style.
	startsep indicates whether we should start with a separator or not"""
	result = ""
	first = True
	for o in model.objects:
		for v in o.type.variables:
			if not first or startsep:
				result += ", "
			else:
				first = False
			result += o.name + "'" + v.name
		for sm in o.type.statemachines:
			for v in sm.variables:
				if not first or startsep:
					result += ", "
				else:
					first = False
				result += o.name + "'" + sm.name + "'" + v.name
	for ch in model.channels:
		if ch.synctype == 'async':
			if not first or startsep:
				result += ", "
			else:
				first = False
			result += ch.name + "'buffer, " + ch.name + "'size"
	return result

def mcrl2_model_vars_with_types(m, startsep):
	"""Return a string containing the names of the variables in the given model with their types, mCRL2 style.
	startsep indicates whether we should start with a separator or not"""
	result = ""
	first = True
	for o in model.objects:
		for v in o.type.variables:
			if not first or startsep:
				result += ", "
			else:
				first = False
			result += o.name + "'" + v.name + ": " + mcrl2type(v.type)
		for sm in o.type.statemachines:
			for v in sm.variables:
				if not first or startsep:
					result += ", "
				else:
					first = False
				result += o.name + "'" + sm.name + "'" + v.name + ": " + mcrl2type(v.type)
	for ch in model.channels:
		if ch.synctype == 'async':
			if not first or startsep:
				result += ", "
			else:
				first = False
			result += ch.name + "'buffer"
			result += ": List(M'"
			for t in mcrl2typetuple(ch.type):
				result += datatypeacronym(t)
			result += "), " + ch.name + "'size: Int"
	return result

def expression(s,stm,c,primmap, owner):
	"""Maps SLCO expression to mCRL2 expression. Statemachine stm and Class c owning the statement are also given. Primmap is a dictionary for rewriting primaries.
	Owner is the class/object owning the statement."""
	global actions, scopedvars
	output = ''
	# special case: s is a variableref. In this case, it is the left-hand side of an assignment, and s refers to an array
	if s.__class__.__name__ == "Variable":
		output = primmap.get(s.name, owner.name + "'" + scopedvars[c.name + "'" + stm.name][s.name])
	if s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2":
		#if s.op != '':
		#	output = '('
		if s.op != '' and s.op != 'xor':
			output += expression(s.left,stm,c,primmap,owner) + " " + operator(s.op) + " " + expression(s.right,stm,c,primmap,owner)
		elif s.op == 'xor':
			output += operator(s.op) + '(' + expression(s.left,stm,c,primmap,owner) + ', ' + expression(s.right,stm,c,primmap,owner) + ')'
		else:
			output += expression(s.left,stm,c,primmap,owner)
	elif s.__class__.__name__ == "ExprPrec1":
		if s.op != '':
			output += operator(s.op) + '(' + expression(s.left,stm,c,primmap,owner) + ', ' + expression(s.right,stm,c,primmap,owner) + ')'
		else:
			output += expression(s.left,stm,c,primmap,owner)
	elif s.__class__.__name__ == "Primary":
		output = operator(s.sign)
		if s.value != None:
			newvalue = s.value
			output += str(newvalue).lower()
		elif s.ref != None:
			if s.ref.ref in actions:
				output += s.ref.ref
			else:
				# is an index to an array given?
				if s.ref.index != None:
					varname = scopedvars[c.name + "'" + stm.name][s.ref.ref]
					varname_with_index = varname + "[" + expression(s.ref.index,stm,c,primmap,owner) + "]"
					if primmap.get(varname_with_index) != None:
						output += primmap.get(varname_with_index)
						return output
				if s.ref.index != None:
					output += "("
				output += primmap.get(scopedvars[c.name + "'" + stm.name][s.ref.ref], owner.name + "'" + scopedvars[c.name + "'" + stm.name][s.ref.ref])
				if s.ref.index != None:
					output += ".Int2Nat(" + expression(s.ref.index,stm,c,primmap,owner) + "))"
		else:
			output += '(' + expression(s.body,stm,c,primmap,owner) + ')'
	return output

def expression_usedvars(s,stm,c,owner):
	"""Produces list of variables occurring in the given expression. This method is different from 'expression_varset', which is used for variable references w.r.t. race condition checking.
	The current function is used to get a complete overview of the used variables, not ignoring any that are irrelevant for race condition checking.
	The function can be called with 'owner' being a class or an object. Depending on this, the names of the variables are given with class-based or object-based scope."""
	output = expression_usedvars_scan(s,stm,c)
	olist = sorted(list(output))

	olist_scoped = []
	for v in olist:
		olist_scoped.append(owner.name + "'" + v)
	return olist_scoped

def expression_usedvars_scan(s,stm,c):
	"""Scanning method to actually recursively detect variable references in a given expression"""
	global actions, scopedvars
	output = set([])
	if s.__class__.__name__ == "VariableRef":
		# is the variable not local to state machine?
		output.add(scopedvars[c.name + "'" + stm.name][s.var.name])
		if s.index != None:
			output |= expression_usedvars_scan(s.index,stm,c)
	elif s.__class__.__name__ != "Primary":
		output |= expression_usedvars_scan(s.left,stm,c)
		if s.op != '':
			output |= expression_usedvars_scan(s.right,stm,c)
	else:
		if s.ref != None:
			print(s.ref.ref)
			if s.ref.ref not in actions:
				print(scopedvars)
				output.add(scopedvars[c.name + "'" + stm.name][s.ref.ref])
				print(output)
				if s.ref.index != None:
					output |= expression_usedvars_scan(s.ref.index,stm,c)
	return output

def expression_varset(s,stm,c,primmap,owner):
	"""Produces set of variables referenced in given SLCO expression or variableref. Statemachine stm and Class c owning the statement are also given. Primmap is a dictionary for rewriting primaries, which is relevant when array indices are used.
	The owner of the statement is also given."""
	global actions, scopedvars, smlocalvars
	output = set([])
	if s.__class__.__name__ == "VariableRef":
		# is the variable not local to state machine?
		if s.var.name not in smlocalvars.get(c.name + "'" + stm.name,set([])):
			varname = owner.name + "'" + s.var.name
			if s.index != None:
				varname += "(Int2Nat(" + expression(s.index,stm,c,primmap,owner) + "))"
				output |= expression_varset(s.index,stm,c,primmap,owner)
			output.add(varname)
	elif s.__class__.__name__ != "Primary":
		output |= expression_varset(s.left,stm,c,primmap,owner)
		if s.op != '':
			output |= expression_varset(s.right,stm,c,primmap,owner)
	else:
		if s.ref != None:
			if s.ref.ref not in actions:
				# IGNORE STATE MACHINE LOCAL VARS!
				if s.ref.ref not in smlocalvars.get(c.name + "'" + stm.name,set([])):
					varname = owner.name + "'" + s.ref.ref
					if s.ref.index != None:
						varname += "(Int2Nat(" + expression(s.ref.index,stm,c,primmap,owner) + "))"
						output |= expression_varset(s.ref.index,stm,c,primmap,owner)
					output.add(varname)
	return output

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

def expression_mcrl2type(s,stm,c):
	"""Provide the mCRL2 type of the given expression"""
	global vartypes
	vlist = expression_usedvars(s,stm,c,c)
	type = ""
	first = True
	for v in vlist:
		if not first:
			type += "# "
		else:
			first = False
		type += mcrl2type(vartypes[v])
	type += " -> Bool"
	return type

def statement_condition_mcrl2type(s):
	"""Provide the type of the condition associated to the given statement"""
	global statemachine, smclass, porttypes
	result = ""
	if s.__class__.__name__ == "Expression":
		result += expression_mcrl2type(s, statemachine[s], smclass[statemachine[s]])
	elif s.__class__.__name__ == "SendSignal" or s.__class__.__name__ == "ReceiveSignal":
		ctype = porttypes[smclass[statemachine[s]].name + "'" + s.target.name]
		acronym = ""
		for t in ctype:
			acronym += datatypeacronym(mcrl2type(t))
		result += "List(M'" + acronym + ")"
		if s.__class__.__name__ == "SendSignal":
			result += " # Int # Int"
		if s.__class__.__name__ == "ReceiveSignal":
			if s.guard != None:
				types = expression_mcrl2type(s.guard, statemachine[s], smclass[statemachine[s]])
				if types != "":
					result += " # " + types
			else:
				result += " -> Bool"
		else:
			result += " -> Bool"
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			result += expression_mcrl2type(s.guard, statemachine[s], smclass[statemachine[s]])
	return result

def statement_condition_varlist(s):
	"""Provide the list of variables of the condition associated to the given statement"""
	global statemachine, smclass, porttypes, vartypes
	result = ""
	if s.__class__.__name__ == "Expression":
		vlist = expression_usedvars(s, statemachine[s], smclass[statemachine[s]], smclass[statemachine[s]])
		first = True
		for v in vlist:
			if not first:
				result += ", "
			else:
				first = False
			result += v + ": " + mcrl2type(vartypes[v])
	elif s.__class__.__name__ == "SendSignal" or s.__class__.__name__ == "ReceiveSignal":
		ctype = porttypes[smclass[statemachine[s]].name + "'" + s.target.name]
		acronym = ""
		for t in ctype:
			acronym += datatypeacronym(mcrl2type(t))
		result += "ch'buffer: List(M'" + acronym + ")"
		if s.__class__.__name__ == "SendSignal":
			result += ", ch'size: Int, ch_max: Int"
		if s.__class__.__name__ == "ReceiveSignal":
			if s.guard != None:
				print("here")
				vlist = expression_usedvars(s.guard, statemachine[s], smclass[statemachine[s]], smclass[statemachine[s]])
				print("output: " + str(vlist))
				for v in vlist:
					result += " # " + v + ": " + mcrl2type(vartypes[v]) 
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			result +=  statement_condition_varlist(s.guard)
	return result

def statement_condition(s, owner):
	"""Provide the condition associated to the given statement. Owner is the owner of statement s."""
	global statemachine, smclass, porttypes, ochannel
	result = ""
	if s.__class__.__name__ == "Expression":
		if not expression_is_actionref(s):
			result += expression(s, statemachine[s], smclass[statemachine[s]], {}, owner)
	elif s.__class__.__name__ == "SendSignal" or s.__class__.__name__ == "ReceiveSignal":
		if ochannel[owner][s].synctype == "async":
			if s.__class__.__name__ == "SendSignal":
				result += ochannel[owner][s].name + "'size < " + ochannel[owner][s].name + "'max"
			if s.__class__.__name__ == "ReceiveSignal":
				result += ochannel[owner][s].name + "'size != 0 && el'0(head(" + ochannel[owner][s].name + "'buffer)) == " + s.signal
				if s.guard != None:
					# create dictionary to translate primaries to correct parts of the next message on the channel
					newdict = {}
					for i in range(0, len(s.params)):
						varname = s.params[i].var.name
						if s.params[i].index != None:
							varname += "[" + expression(s.params[i].index,statemachine[s],smclass[statemachine[s]],{},owner) + "]"
						newdict[varname] = "el'" + str(i+1) + "(head(" + ochannel[owner][s].name + "'buffer))"
					result += " && " + expression(s.guard, statemachine[s], smclass[statemachine[s]], newdict, owner)
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			result += expression(s.guard, statemachine[s], smclass[statemachine[s]], {}, owner)
	return result

def sync_statement_condition(s_rcv, rcv_owner, s_snd, snd_owner):
	"""Provide condition for the syncing of the given send and receive statements. Precondition is that s_snd is of type SendSignal, and s_rcv is of type ReceiveSignal.
	Furthermore, it is assumed that their Signals match."""
	global statemachine, smclass
	result = ""
	if s_rcv.guard != None:
		# create dictionary to translate primaries to correct parts of the next message on the channel
		newdict = {}
		for i in range(0, len(s_rcv.params)):
			varname = s_rcv.params[i].var.name
			if s_rcv.params[i].index != None:
				varname += "[" + s_rcv.params[i].index + "]"
			varname2 = ""
			if s_snd.params[i].index != None:
				varname2 += "("
			varname2 += s_snd.params[i].var.name
			if s_snd.params[i].index != None:
				varname2 += ".Int2Nat(" + expression(s_snd.params[i].index,statemachine[s_snd],smclass[statemachine[s_snd]],{},snd_owner) + "))" 
			newdict[varname] = varname2
		result += " && " + expression(s_rcv.guard, statemachine[s_rcv], smclass[statemachine[s_rcv]], newdict, rcv_owner)
	return result

def statementstatechanges(s,o):
	"""Maps SLCO statement effects to mCRL2 state changes. Object o owning the statement is also given"""
	global porttypes, vardict, scopedvars, statemachine, ochannel
	output = ''
	if s.__class__.__name__ == "Assignment":
		varname = scopedvars[o.type.name + "'" + statemachine[s].name][s.left.var.name]
		# an assignment to an array cell should be handled differently from other cases
		if s.left.index != None:
			output = ", " + o.name + "'" + varname + "=update(" + varname + ",Int2Nat(" + expression(s.left.index,statemachine[s],o.type,{},o) + "),"
			# in case we are updating a Byte, restrict the new value
			eright = expression(s.right,statemachine[s],o.type,{},o)
			if s.left.var.type.base == 'Byte':
				eright = "(" + eright + ") mod 256"
			output += eright + ")"
		else:
			output = ", " + o.name + "'" + varname
			eright = expression(s.right,statemachine[s],o.type,{},o)
			if s.left.var.type.base == 'Byte':
				eright = "(" + eright + ") mod 256"
			output += "=" + eright
	elif s.__class__.__name__ == "Composite":
		# first build vardict for sequence of assignments
		vardict = {}
		for e in s.assignments:
			newright = expression(e.right,statemachine[s],o.type,vardict,o)
			# in case we are updating a Byte, restrict the new value
			if e.left.var.type.base == 'Byte':
				newright = "(" + newright + ") mod 256"
			varname = scopedvars[o.type.name + "'" + statemachine[s].name][e.left.var.name]
			if e.left.index != None:
				vardict[varname] = "update(" + expression(e.left.var,statemachine[s],o.type,vardict,o) + ",Int2Nat(" + expression(e.left.index,statemachine[s],o.type,vardict,o) + ")," + newright + ")"
			else:
				vardict[varname] = "(" + newright + ")"
		# add assignments to state changes
		for key, value in vardict.items():
			output += ", " + o.name + "'" + key + "=" + value
	elif s.__class__.__name__ == "Delay":
		output = ""
	elif s.__class__.__name__ == "SendSignal":
		output = ", " + ochannel[o][s].name + "'buffer=" + ochannel[o][s].name + "'buffer ++ [m'"
		for t in mcrl2typetuple(ochannel[o][s].type):
			output += datatypeacronym(t)
		output += "(" + s.signal
		for p in s.params:
			output += ", "
			output += expression(p,statemachine[s],o.type,{},o)
		output += ")], " + ochannel[o][s].name + "'size=" + ochannel[o][s].name + "'size+1"
	elif s.__class__.__name__ == "ReceiveSignal":
		vardict = {}
		for i in range(0,len(s.params)):
			p = s.params[i]
			newright = "el'" + str(i+1) + "(head(" + ochannel[o][s].name + "'buffer))"
			# in case we are updating a Byte, restrict the new value
			if p.var.type.base == 'Byte':
				newright = "(" + newright + ") mod 256"
			varname = scopedvars[o.type.name + "'" + statemachine[s].name][p.var.name]
			if p.index != None:
				vardict[varname] = "update(" + expression(p.var,statemachine[s],o.type,vardict,o) + ",Int2Nat(" + expression(p.index,statemachine[s],o.type,vardict,o) + ")," + newright + ")"
			else:
				vardict[varname] = "(" + newright + ")"
		# add assignments
		for key, value in vardict.items():
			output += ", " + o.name + "'" + key + "=" + value
		output += ", " + ochannel[o][s].name + "'buffer=tail(" + ochannel[o][s].name + "'buffer), " + ochannel[o][s].name + "'size=" + ochannel[o][s].name + "'size-1"
	elif s.__class__.__name__ == "Expression":
		output = ""
	return output

def sync_statementstatechanges(s_rcv,o_rcv,s_snd,o_snd):
	"""Maps SLCO syncing statements effects to mCRL2 state changes. Objects o owning the statements are also given.
	Preconditions: the statements are of the right types, and the Signals match."""
	global porttypes, scopedvars, statemachine
	pindex = 0
	output = ""
	vardict = {}
	for i in range(0,len(s_rcv.params)):
		p = s_rcv.params[i]
		newright = expression(s_snd.params[i],statemachine[s_snd],o_snd.type,{},o_snd)
		# in case we are updating a Byte, restrict the new value
		if p.var.type.base == 'Byte':
			newright = "(" + newright + ") mod 256"
		varname = scopedvars[o_rcv.type.name + "'" + statemachine[s_rcv].name][p.var.name]
		if p.index != None:
			vardict[varname] = "update(" + expression(p.var,statemachine[s_rcv],o_rcv.type,vardict,o_rcv) + ",Int2Nat(" + expression(p.index,statemachine[s_rcv],o_rcv.type,vardict,o_rcv) + ")," + newright + ")"
		else:
			vardict[varname] = "(" + newright + ")"
	# add assignments
	for key, value in vardict.items():
		output += ", " + o_rcv.name + "'" + key + "=" + value
	return output

def statement_accesspattern(s, o):
	"""Provide the access pattern of the given statement. o is Object owning statement s."""
	global statemachine, smclass

	if s.__class__.__name__ == "Assignment":
		readset = expression_varset(s.right,statemachine[s],smclass[statemachine[s]],{},o)
		writeset = expression_varset(s.left,statemachine[s],smclass[statemachine[s]],{},o)
		return tuple([readset, writeset])
	elif s.__class__.__name__ == "Composite":
		vardict = {}
		readset = set([])
		writeset = set([])
		if s.guard != None:
			readset |= expression_varset(s.guard,statemachine[s],smclass[statemachine[s]],vardict,o)
		for st in s.assignments:
			readset |= expression_varset(st.right,statemachine[s],smclass[statemachine[s]],vardict,o)
			writeset |= expression_varset(st.left,statemachine[s],smclass[statemachine[s]],vardict,o)
			# update vardict (to correctly handle possible array index use in subsequent assignments)
			newright = expression(st.right,statemachine[s],smclass[statemachine[s]],vardict,o)
			varname = scopedvars[smclass[statemachine[s]].name + "'" + statemachine[s].name][st.left.var.name]
			if st.left.index != None:
				vardict[varname] = "update(" + expression(st.left.var,statemachine[s],smclass[statemachine[s]],vardict,o) + ",Int2Nat(" + expression(st.left.index,statemachine[s],smclass[statemachine[s]],vardict,o) + ")," + newright + ")"
			else:
				vardict[varname] = "(" + newright + ")"
		return tuple([readset, writeset])
	elif s.__class__.__name__ == "Delay":
		return tuple([set([]),set([])])
	elif s.__class__.__name__ == "SendSignal":
		readset = set([])
		for st in s.params:
			readset |= expression_varset(st,statemachine[s],smclass[statemachine[s]],{},o)
		return tuple([readset, set([])])
	elif s.__class__.__name__ == "ReceiveSignal":
		writeset = set([])
		for st in s.params:
			writeset |= expression_varset(st,statemachine[s],smclass[statemachine[s]],{},o)
		readset = set([])
		if s.guard != None:
			readset = expression_varset(s.guard,statemachine[s],smclass[statemachine[s]],{},o)
		# in SLCO ReceiveSignal, it is not possible to refer to the old value of a variable to which you are reading. Hence, reading AND writing to the same variable cannot occur
		readset = readset - writeset
		return tuple([readset, writeset])
	elif s.__class__.__name__ == "Expression":
		if expression_is_actionref(s):
			return tuple([set([]), set([])])
		else:
			readset = expression_varset(s,statemachine[s],smclass[statemachine[s]],{},o)
			return tuple([readset, set([])])

def statement_condition_accesspattern(s, o):
	"""Provide the access pattern of the condition of the given statement. o is Object owning statement s."""
	global statemachine, smclass

	if s.__class__.__name__ == "Assignment":
		return tuple([set([]), set([])])
	elif s.__class__.__name__ == "Composite":
		readset = set([])
		if s.guard != None:
			readset |= expression_varset(s.guard,statemachine[s],smclass[statemachine[s]],{},o)
		return tuple([readset, set([])])
	elif s.__class__.__name__ == "Delay":
		return tuple([set([]),set([])])
	elif s.__class__.__name__ == "SendSignal":
		return tuple([set([]),set([])])
	elif s.__class__.__name__ == "ReceiveSignal":
		writeset = set([])
		for st in s.params:
			writeset |= expression_varset(st,statemachine[s],smclass[statemachine[s]],{},o)
		readset = set([])
		if s.guard != None:
			readset = expression_varset(s.guard,statemachine[s],smclass[statemachine[s]],{},o)
		# in SLCO ReceiveSignal, it is not possible to refer to the old value of a variable to which you are reading. Hence, reading AND writing to the same variable cannot occur
		readset = readset - writeset
		return tuple([readset, set([])])
	elif s.__class__.__name__ == "Expression":
		if expression_is_actionref(s):
			return tuple([set([]), set([])])
		else:
			readset = expression_varset(s,statemachine[s],smclass[statemachine[s]],{},o)
			return tuple([readset, set([])])

def compute_accesspatterns(m):
	"""Compute the access patterns for all statements in the system"""
	adict = {}
	for o in m.objects:
		adict[o] = {}
		for stm in o.type.statemachines:
			for tr in stm.transitions:
				for st in tr.statements:
					access = statement_accesspattern(st,o)
					adict[o][st] = access
	return adict

def compute_condition_accesspatterns(m):
	"""Compute the access patterns for all statements in the system"""
	adict = {}
	for o in m.objects:
		adict[o] = {}
		for stm in o.type.statemachines:
			for tr in stm.transitions:
				for st in tr.statements:
					access = statement_condition_accesspattern(st,o)
					adict[o][st] = access
	return adict

def mcrl2_accesspattern(s, o, b):
	"""Return the access pattern of the given statement for use in an mCRL2 specification. Owner o is also given.
	Boolean b indicates whether the statement should be considered as enabled or not."""
	global statement_access, statement_condition_access
	if b:
		access = statement_access[o][s]
	else:
		access = statement_condition_access[o][s]
	output = "AP'("
	sorted_access = sorted(list(access[0]))
	# if the list requires dynamic sorting (it contains more than one dynamic accesses to an array), indicate this
	occcurrences = set([])
	found = False
	for v in sorted_access:
		v_splitted = v.split(".Int2Nat(")
		if len(v_splitted) > 1:
			if not RepresentsInt(v_splitted[1][:-1]):
				if v_splitted[0] in occurrences:
					found = True
					break
				else:
					occurrences.add(v_splitted[0])
	if found:
		output += "sorted_array_accesses("
	output += "["
	first = True
	for v in sorted_access:
		if not first:
			output += ", "
		else:
			first = False
		output += mcrl2varprefix + v
	output += "]"
	if found:
		output += ")"
	output += ", "
	sorted_access = sorted(list(access[1]))
	found = False
	for v in sorted_access:
		v_splitted = v.split(".Int2Nat(")
		if len(v_splitted) > 1:
			if not RepresentsInt(v_splitted[1][:-1]):
				if v_splitted[0] in occurrences:
					found = True
					break
				else:
					occurrences.add(v_splitted[0])
	if found:
		output += "sorted_array_accesses("
	output += "["
	first = True
	for v in sorted_access:
		if not first:
			output += ", "
		else:
			first = False
		output += mcrl2varprefix + v
	output += "]"
	if found:
		output += ")"
	output += ")"
	return output

def mcrl2_read_accesspattern(s, o, b):
	"""Return the read access pattern of the given statement for use in an mCRL2 specification. Owner o is also given.
	Boolean b indicates whether the statement should be considered as enabled or not."""
	global statement_access, statement_condition_access
	if b:
		access = statement_access[o][s]
	else:
		access = statement_condition_access[o][s]
	output = "{"
	first = True
	sorted_access = sorted(list(access[0]))
	for v in sorted_access:
		if not first:
			output += ", "
		else:
			first = False
		output += mcrl2varprefix + v
	output += "}"
	return output

def mcrl2_write_accesspattern(s, o, b):
	"""Return the write access pattern of the given statement for use in an mCRL2 specification. Owner o is also given.
	Boolean b indicates whether the statement should be considered as enabled or not."""
	global statement_access, statement_condition_access
	if b:
		access = statement_access[o][s]
	else:
		access = statement_condition_access[o][s]
	output = "{"
	first = True
	sorted_access = sorted(list(access[1]))
	for v in sorted_access:
		if not first:
			output += ", "
		else:
			first = False
		output += mcrl2varprefix + v
	output += "}"
	return output

def statement_is_safe(s):
	"""Returns whether the given statement is safe (w.r.t. race conditions) or not"""
	global safe_statements
	return s in safe_statements

def compare_accesses2(s1, s2, limit):
	"""Compare two access patterns. Both consist of a set and a dictionary, one providing all simple accesses and exact (statically clear) array accesses. The other with representations of all imprecise array accesses.
	The question is whether at least 'limit' access matches can be made. As soon as this limit is reached, True is returned, otherwise False."""
	# first count size of intersection of the first sets
	count = len(s1[0] & s2[0])
	if count >= limit:
		return True
	# determine the largest number of possible combinations of precise/imprecise array accesses
	# collect the arrays that are accessed by the first pattern
	aset = set([a for a in s1[1].keys()]) | set([a for a in s1[2].keys()])
	for a in aset:
		# first compare precise array accesses
		precise_match = len(s1[1].get(a,set([])) & s2[1].get(a,set([])))
		count += precise_match
		if count >= limit:
			return True
		# how many precise accesses are left?
		remainder1 = max(0, len(s1[1].get(a,set([]))) - precise_match)
		remainder2 = max(0, len(s2[1].get(a,set([]))) - precise_match)
		# match remaining precise accesses with imprecise accesses
		imprecise_match1 = min(s2[2].get(a,0), remainder1)
		imprecise_match2 = min(s1[2].get(a,0), remainder2)
		count += imprecise_match1 + imprecise_match2
		if count >= limit:
			return True
		# finally, match remaining imprecise accesses with each other
		imprecise_remainder1 = max(0,s1[2].get(a,0) - imprecise_match2)
		imprecise_remainder2 = max(0,s2[2].get(a,0) - imprecise_match1)
		count += min(imprecise_remainder1, imprecise_remainder2)
		if count >= limit:
			return True
	return count >= limit

def compare_accesses3(s1, s2, s3, limit):
	"""Compare three access patterns"""
	count = len(s1[0] & s2[0] & s3[0])
	if count >= limit:
		return True
	# determine the largest number of possible combinations of precise/imprecise array accesses
	# collect the arrays that are accessed by the first pattern
	aset = set([a for a in s1[1].keys()]) | set([a for a in s1[2].keys()])
	for a in aset:
		# first compare precise array accesses
		precise_match = len(s1[1].get(a,set([])) & s2[1].get(a,set([])) & s3[1].get(a,set([])))
		count += precise_match
		if count >= limit:
			return True
		# how many precise accesses are left?
		remainder1 = max(0, len(s1[1].get(a,set([]))) - precise_match)
		remainder2 = max(0, len(s2[1].get(a,set([]))) - precise_match)
		remainder3 = max(0, len(s3[1].get(a,set([]))) - precise_match)
		# match remaining precise accesses with imprecise accesses
		imprecise_counter1 = s1[2].get(a,0)
		imprecise_counter2 = s2[2].get(a,0)
		imprecise_counter3 = s3[2].get(a,0)
		imprecise_match1 = min(remainder1, imprecise_counter2, imprecise_counter3)
		# update number of imprecise accesses left
		imprecise_counter2 -= imprecise_match1
		imprecise_counter3 -= imprecise_match1
		imprecise_match2 = min(remainder2, imprecise_counter1, imprecise_counter3)
		# update number of imprecise accesses left
		imprecise_counter1 -= imprecise_match2
		imprecise_counter3 -= imprecise_match2
		imprecise_match3 = min(remainder3, imprecise_counter1, imprecise_counter2)
		# update number of imprecise accesses left
		imprecise_counter1 -= imprecise_match3
		imprecise_counter2 -= imprecise_match3
		count += imprecise_match1 + imprecise_match2 + imprecise_match3
		if count >= limit:
			return True
		# finally, match remaining imprecise accesses with each other
		count += min(imprecise_counter1, imprecise_counter2, imprecise_counter3)
		if count >= limit:
			return True
	return count >= limit

def number_of_accesses(s):
	"""Count the number of accesses"""
	count = len(s[0])
	for a in s[1].keys():
		count += len(s[1][a])
	for a in s[2].keys():
		count += s[2][a]
	return count

def identify_safe_unsafe_statements(m):
	"""Partition the statements of the model into safe and unsafe statements"""
	global safe_statements, unsafe_statements, statement_access, statemachine, smclass, unsafe_variables

	# Distribute statements over the sets safe and unsafe
	safe_statements = set([])
	unsafe_statements = set([])

	# create list of object, one at most per class
	classobjects = []
	represented_classes = set([])
	for o in model.objects:
		if o.type not in represented_classes:
			classobjects.append(o)
			represented_classes.add(o.type)

	# filter statement_access to remove references to array cells that cannot be (or are hard to be) evaluated statically
	# for each access set (read and write) we actually build a set and two dictionaries:
	# - the first set consists of accesses to simple, i.e., not array, variables
	# - the first dictionary produces per accessed array a set of concrete indices (integers)
	# - the second dictionary produces per accessed array the number of accesses where the location (cell index) could not be determined statically.
	filtered_statement_access = {}
	for o in statement_access.keys():
		filtered_statement_access[o] = {}
		for st in statement_access[o].keys():
			newaccess = [[set([]), {}, {}], [set([]), {}, {}]]
			for i in range(0,2):
				imprecise_seen = set([])
				for v in statement_access[o][st][i]:
					varname = v
					if v.find('.Int2Nat(') != -1:
						varname, varindex = v.split('.Int2Nat(')
						# get index
						varindex = varindex[:-1]
						if RepresentsInt(varindex):
							occset = newaccess[i][1].get(varname,set([]))
							occset.add(varindex)
							newaccess[i][1][varname] = occset
						elif (varname + "[" + varindex + "]") not in imprecise_seen:
							imprecise_seen.add(varname + "[" + varindex + "]")
							counter = newaccess[i][2].get(varname,0)
							counter += 1
							newaccess[i][2][varname] = counter
					else:
						newaccess[i][0].add(varname)
			filtered_statement_access[o][st] = tuple(newaccess)

	# create dictionary of statements and remove trivially safe transitions
	sdict = {}
	for o in classobjects:
		c = o.type
		cdict = {}
		for sm in c.statemachines:
			stset = set([])
			for tr in sm.transitions:
				for st in tr.statements:
					if number_of_accesses(filtered_statement_access[o][st][0]) <= 1 and number_of_accesses(filtered_statement_access[o][st][1]) == 0:
						safe_statements.add(st)
					else:
						stset.add(st)
			cdict[sm] = stset
		sdict[c] = cdict

	# check possibility for race conditions
	for o in classobjects:
		c = o.type
		for i in range(0,len(c.statemachines)):
			stset1 = sdict[c][c.statemachines[i]]
			removed1 = set([])
			for j in range(i+1,len(c.statemachines)):
				stset2 = sdict[c][c.statemachines[j]]
				removed2 = set([])
				for st1 in stset1:
					for st2 in stset2:
						if compare_accesses2(filtered_statement_access[o][st1][1], filtered_statement_access[o][st2][0], 2) or compare_accesses2(filtered_statement_access[o][st1][0], filtered_statement_access[o][st2][1], 2):
							removed1.add(st1)
							removed2.add(st2)
						elif compare_accesses2(filtered_statement_access[o][st1][1], filtered_statement_access[o][st2][1], 2):
							removed1.add(st1)
							removed2.add(st2)
						elif compare_accesses3(filtered_statement_access[o][st1][0], filtered_statement_access[o][st1][1], filtered_statement_access[o][st2][1], 1) or compare_accesses3(filtered_statement_access[o][st2][0], filtered_statement_access[o][st2][1], filtered_statement_access[o][st1][1], 1):
							removed1.add(st1)
							removed2.add(st2)
					stset2 -= removed2
					unsafe_statements |= removed2
				stset1 -= removed1
				unsafe_statements |= removed1


	# for each class, create dependency graph, detect non-trivial SCCs, and mark involved statements as unsafe
	for o in classobjects:
		c = o.type
		# create write dictionary
		wdict = {}
		for sm in c.statemachines:
			for tr in sm.transitions:
				for st in tr.statements:
					for v in filtered_statement_access[o][st][1][0]:
						wr = wdict.get(v,set([]))
						wr.add(st)
						wdict[v] = wr
					for v in filtered_statement_access[o][st][1][1].keys():
						v_indices = filtered_statement_access[o][st][1][1][v]
						wr_arraydict = wdict.get(v + "_indexed", {})
						for i in v_indices:
							iset = wr_arraydict.get(i, set([]))
							iset.add(st)
							wr_arraydict[i] = iset
						wdict[v] = wr_arraydict
					for v in filtered_statement_access[o][st][1][2].keys():
						wr = wdict.get(v,set([]))
						wr.add(st)
						wdict[v] = wr

		depgraph = {}
		for sm in c.statemachines:
			for tr in sm.transitions:
				for st in tr.statements:
					stoutgoing = set([])
					for v in filtered_statement_access[o][st][0][0]:
						stoutgoing |= wdict.get(v,set([]))
					# concrete array read accesses can be matched on other concrete write accesses and inconcrete write accesses to the same array
					for v in filtered_statement_access[o][st][0][1].keys():
						v_indices = filtered_statement_access[o][st][0][1][v]
						wr_indices = wdict.get(v + "_indexed", {})
						for i in v_indices:
							iset = wr_indices.get(i, set([]))
							stoutgoing |= iset
						stoutgoing |= wdict.get(v,set([]))
					# inconcrete array read accesses can be matched on all concrete write accesses and inconcrete write accesses to the same array
					for v in filtered_statement_access[o][st][0][2].keys():
						wr_indices = wdict.get(v + "_indexed", {})
						for i in wr_indices.keys():
							iset = wr_indices.get(i, set([]))
							stoutgoing |= iset
						stoutgoing |= wdict.get(v,set([]))
					depgraph[st] = stoutgoing
		# SCC detection
		SCCs = list()
		initialstatements = set([])
		for sm in c.statemachines:
			for tr in sm.transitions:
				for st in tr.statements:
					if st not in unsafe_statements:
						initialstatements.add(st)
		identifySCCs(depgraph, initialstatements, {}, SCCs)
		for scc in SCCs:
			if scc[0] > 1:
				for st in scc[1].keys():
					unsafe_statements.add(st)
		# finally, all remaining statements are safe
		for sm in c.statemachines:
			for tr in sm.transitions:
				for st in tr.statements:
					if st not in unsafe_statements:
						safe_statements.add(st)
		# now that we have identified the unsafe statements, build a list of unsafe variables
		unsafe_variables = set([])
		for st in unsafe_statements:
			# get the class owning st, and then all objects of that type
			c = smclass[statemachine[st]]
			olist = []
			for o in model.objects:
				if o.type == c:
					olist.append(o)
			# use the representative object to obtain the access pattern of st
			for o in olist:
				if o in classobjects:
					ap = statement_access[o][st]
					break
			unsafe_variables |= ap[0]
			unsafe_variables |= ap[1]
		# make unsafe_variables a sorted list
		unsafe_variables = sorted(list(unsafe_variables))

def preprocess():
	"""preprocessing method"""
	global model, statemachinenames, statemachine, trowner, smlocalvars, states, actions, class_sync_receives, class_sync_sends, trans, smclass, channeltypes, asynclosslesstypes, asynclossytypes, synctypes, porttypes, ochannel, vartypes, object_sync_commpairs, syncing_statements, sorted_variables
	# build dictionaries providing for a given statement the state machine and transition owning it, and for a given state machine, the class owning it
	for c in model.classes:
		for stm in c.statemachines:
			smclass[stm] = c
			for trn in stm.transitions:
				for stat in trn.statements:
					statemachine[stat] = stm
					trowner[stat] = trn
	# for each state machine, add the initial state to its list of states
	for c in model.classes:
		for stm in c.statemachines:
			stm.states = [stm.initialstate] + stm.states
	# fill in types of variables
	for c in model.classes:
		for i in range(0,len(c.variables)):
			if c.variables[i].type == None:
				c.variables[i].type = c.variables[i-1].type
		for sm in c.statemachines:
			for i in range(0,len(sm.variables)):
				if sm.variables[i].type == None:
					sm.variables[i].type = sm.variables[i-1].type
	# add tau action to all transitions without statements
	for c in model.classes:
		for stm in c.statemachines:
			for trn in stm.transitions:
				if len(trn.statements) == 0:
					trn.statements.append("tau'")
	# set sizes of channels to at least one
	for ch in model.channels:
		if ch.size == 0:
			ch.size = 1
	# fix wrong references from transitions to states (scope errors)
	for c in model.classes:
		for sm in c.statemachines:
			sdict = {}
			for s in sm.states:
				sdict[s.name] = s
			for tr in sm.transitions:
				if tr.source != sdict[tr.source.name]:
					tr.source = sdict[tr.source.name]
				if tr.target != sdict[tr.target.name]:
					tr.target = sdict[tr.target.name]
	# build a set of used statemachine names
	statemachinenames = set([])
	for c in model.classes:
		for stm in c.statemachines:
			statemachinenames.add(stm.name)
	# build a dictionary providing the type of messages that can be sent over a given port
	for c in model.channels:
		porttypes[str(c.source.type.name) + "'" + str(c.ports[0].name)] = c.type
		porttypes[str(c.target.type.name) + "'" + str(c.ports[1].name)] = c.type
	# build a dictionary providing sets of variables local for given state machines
	for c in model.classes:
		for stm in c.statemachines:
			varset = set([])
			for var in stm.variables:
				varset.add(var.name)
			smlocalvars[c.name + "'" + stm.name] = varset
	# build dictionary making variable scopes explicit
	for c in model.classes:
		for stm in c.statemachines:
			vdict = {}
			for var in c.variables:
				vdict[var.name] = var.name
			for var in stm.variables:
				vdict[var.name] = stm.name + "'" + var.name
			scopedvars[c.name + "'" + stm.name] = vdict
	# construct dictionary of variables (with class-based scopes) and their types
	vartypes = {}
	for c in model.classes:
		for v in c.variables:
			vartypes[c.name + "'" + v.name] = v.type
			for stm in c.statemachines:
				for v in stm.variables:
					vartypes[c.name + "'" + stm.name + "'" + v.name] = v.type
	# make a set of state names
	states = set([])
	for c in model.classes:
		for stm in c.statemachines:
			for s in stm.states:
				states.add(s.name)
	# make a dictionary of channel types, where for each type we keep track of the encountered signal names
	channeltypes = {}
	
	for c in model.channels:
		type = mcrl2typetuple(c.type)
		channeltypes[type] = set([])
		# add the type to the right set
		if c.synctype == 'async':
			if c.losstype == 'lossless':
				asynclosslesstypes.add(type)
			else:
				asynclossytypes.add(type)
		else:
			synctypes.add(tuple(type))
	# lookup all signal names
	for c in model.classes:
		for stm in c.statemachines:
			for trn in stm.transitions:
				for stat in trn.statements:
					if stat.__class__.__name__ == "ReceiveSignal" or stat.__class__.__name__ == "SendSignal":
						# get type
						ctype = mcrl2typetuple(porttypes[c.name + "'" + stat.target.name])
						signalset = channeltypes[ctype]
						signalset.add(stat.signal)
	# construct the set of actions as they appear in the model
	actions = set([])
	for a in model.actions:
		actions.add(a.name)
	# give transitions without a priority a high enough priority value, such that they actually get the lowest priority
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
	# construct a dictionary that provides the channel linked to a given object/statement pair
	ochannel = {}
	for o in model.objects:
		ochannel[o] = {}
		for sm in o.type.statemachines:
			for tr in sm.transitions:
				for st in tr.statements:
					if st.__class__.__name__ == "ReceiveSignal" or st.__class__.__name__ == "SendSignal":
						for ch in model.channels:
							if ch.source == o and st.target == ch.ports[0]:
								ochannel[o][st] = ch
							elif ch.target == o and st.target == ch.ports[1]:
								ochannel[o][st] = ch
	# construct a dictionary that provides a list of (object, send statement) pairs linked to a given channel
	channelsends = {}
	for o in model.objects:
		for sm in o.type.statemachines:
			for tr in sm.transitions:
				for st in tr.statements:
					if st.__class__.__name__ == "SendSignal":
						ch = ochannel[o][st]
						if ch.synctype == 'sync':
							pset = channelsends.get(ch, set([]))
							pset.add(tuple([o, st]))
							channelsends[ch] = pset
	# construct dictionary of statements, indicating with which other statements synchronous communication can be done
	syncing_statements = {}
	for o in model.objects:
		syncing_statements[o] = {}
		for sm in o.type.statemachines:
			for tr in sm.transitions:
				for st in tr.statements:
					syncing_statements[o][st] = set([])
	for o in model.objects:
		for sm in o.type.statemachines:
			for tr in sm.transitions:
				for st in tr.statements:
					if st.__class__.__name__ == "ReceiveSignal":
						ch = ochannel[o][st]
						if ch.synctype == "sync":
							if o == ch.source and st.target == ch.ports[0]:
								snd_object = ch.target
								snd_port = ch.ports[1]
							else:
								snd_object = ch.source
								snd_port = ch.ports[0]
							sends = channelsends[ch]
							for snd in sends:
								if snd_object == snd[0] and snd_port == snd[1].target and st.signal == snd[1].signal:
									syncing_statements[snd[0]][snd[1]].add(tuple([o,st]))

	# construct the transition relation of the state machines in a dictionary
	trans = {}
	for c in model.classes:
		ctrans = {}
		for sm in c.statemachines:
			smtrans = {}
			for s in sm.states:
				smtrans[s] = []
			for tr in sm.transitions:
				smtrans[tr.source].append(tr)
			ctrans[sm] = smtrans
		trans[c] = ctrans
	# construct set of object pairs that are involved in communication, i.e., a pair (o1, o2) indicates that there is a channel from o1 to o2
	object_sync_commpairs = set([])
	for ch in model.channels:
		if ch.synctype == 'sync':
			pair = tuple([ch.source, ch.target])
			object_sync_commpairs.add(pair)
			pair = tuple([ch.target, ch.source])
			object_sync_commpairs.add(pair)
	# create sorted list of object variables
	tmp_sorted_variables = []
	for o in model.objects:
		for v in o.type.variables:
			tmp_sorted_variables.append(tuple([v, o.name + "'" + v.name, 0]))
	tmp_sorted_variables = sorted(tmp_sorted_variables, key=lambda vartuple: vartuple[1])
	v_index = 0
	sorted_variables = []
	for v in tmp_sorted_variables:
		vlist = list(v)
		vlist[2] = v_index
		sorted_variables.append(tuple(vlist))
		if v[0].type.size > 1:
			v_index += v[0].type.size
		else:
			v_index += 1

def translate():
	"""The translation function"""
	global model, modelname, statemachinenames, statemachine, tr, smlocalvars, states, actions, class_receives, class_sends, vartypes, mcrl2varprefix, channeltypes, asynclossytypes, asynclosslesstypes, synctypes, statement_access, statement_condition_access, unsafe_statements, object_sync_commpairs, syncing_statements, check_onthefly, lock_onthefly, apply_por, sorted_variables, unsafe_variables
	
	path, name = split(modelname)
	if name.endswith('.slco'):
		name = name[:-4]
	else:
		name = name[:-7]
	outFile = open(join(path,name + "mcrl2"), 'w')

	# Initialize the template engine.
	jinja_env = jinja2.Environment(loader=jinja2.FileSystemLoader(this_folder), trim_blocks=True, lstrip_blocks=True, extensions=['jinja2.ext.loopcontrols','jinja2.ext.do',])

	# Register the filters
	jinja_env.filters['mcrl2value'] = mcrl2value
	jinja_env.filters['mcrl2type'] = mcrl2type
	jinja_env.filters['mcrl2typetuple'] = mcrl2typetuple
	jinja_env.filters['datatypeacronym'] = datatypeacronym
	jinja_env.filters['variabledefault'] = variabledefault
	jinja_env.filters['expression'] = expression
	jinja_env.filters['expression_usedvars'] = expression_usedvars
	jinja_env.filters['statement_condition_mcrl2type'] = statement_condition_mcrl2type
	jinja_env.filters['statement_condition_varlist'] = statement_condition_varlist
	jinja_env.filters['statement_condition'] = statement_condition
	jinja_env.filters['statementstatechanges'] = statementstatechanges
	jinja_env.filters['sync_statement_condition'] = sync_statement_condition
	jinja_env.filters['sync_statementstatechanges'] = sync_statementstatechanges
	jinja_env.filters['hasobjectvariables'] = hasobjectvariables
	jinja_env.filters['hascondition'] = hascondition
	jinja_env.filters['statement_is_safe'] = statement_is_safe
	jinja_env.filters['mcrl2_accesspattern'] = mcrl2_accesspattern
	jinja_env.filters['mcrl2_read_accesspattern'] = mcrl2_read_accesspattern
	jinja_env.filters['mcrl2_write_accesspattern'] = mcrl2_write_accesspattern
	jinja_env.filters['mcrl2_model_vartypes'] = mcrl2_model_vartypes
	jinja_env.filters['mcrl2_model_vars'] = mcrl2_model_vars
	jinja_env.filters['mcrl2_model_vars_with_types'] = mcrl2_model_vars_with_types
	
	# Register the tests
	jinja_env.tests['hasvariables'] = hasvariables
	jinja_env.tests['hasindex'] = hasindex
	jinja_env.tests['hasnoindex'] = hasnoindex

	# compute statement access patterns
	statement_access = compute_accesspatterns(model)
	statement_condition_access = compute_condition_accesspatterns(model)
	# compute which statements are safe and unsafe
	identify_safe_unsafe_statements(model)

	# special case: if no unsafe statements are present, the result is that all variables can remain unlocked
	if len(unsafe_statements) == 0:
		print("No variables require locking!")
		exit(0)

	# Produce (guard, action, effect) tuples for the translation
	# produce_summands(model)
	# load the mCRL2 template
	template = jinja_env.get_template('mcrl2sr.jinja2template')
	out = template.render(model=model, statemachinenames=statemachinenames, states=states, vartypes=vartypes, mcrl2varprefix=mcrl2varprefix, channeltypes=channeltypes, asynclosslesstypes=asynclosslesstypes, asynclossytypes=asynclossytypes, synctypes=synctypes, trans=trans, ochannel=ochannel, object_sync_commpairs=object_sync_commpairs, syncing_statements=syncing_statements, transowner=trowner, statemachine=statemachine, check_onthefly=check_onthefly, lock_onthefly=lock_onthefly, apply_por=apply_por, sorted_variables=sorted_variables, unsafe_variables=unsafe_variables)
	# write mCRL2 spec
	outFile.write(out)
	outFile.close()

def main(args):
	"""The main function"""
	global modelname, model, check_onthefly, apply_por, lock_onthefly
	if len(args) == 0:
		print("Missing argument: SLCO model")
		sys.exit(1)
	else:
		if args[0] == '-h' or args[0] == '-help':
			print("Usage: pypy/python3 slco2mcrl2 [-rc]")
			print("")
			print("Transform an SLCO 2.0 model to an mCRL2 model for race condition checking (reduced state space).")
			print(" -o                                    apply on-the-fly race condition checking")
			print(" -l                                    lock on-the-fly (applies checking on-the-fly and acts on result)")
			print(" -r                                    apply partial-order reduction")
			sys.exit(0)
		else:
			for i in range(0,len(args)):
				if args[i] == '-o':
					check_onthefly = True
				elif args[i] == '-r':
					apply_por = True
				elif args[i] == '-l':
					lock_onthefly = True
					check_onthefly = True
				else:
					modelname = args[i]

	# create meta-model
	slco_mm = metamodel_from_file(join(this_folder,'slco2.tx'))

	batch = []
	if modelname.endswith('.slco'):
		batch = [modelname]
	else:
		batch = glob.glob(join(this_folder, modelname, "*.slcotxt"))

	if not batch:
		exit(1)

	#gen_dir = "generated_mcrl2"
	#dir = dirname(batch[0])
	#gen_folder = join(dir, gen_dir)
	#if exists(gen_folder):
	#	rmtree(gen_folder)
	#mkdir(gen_folder)

	for file in batch:
		# read model
		modelname = file
		model = slco_mm.model_from_file(file)
		print("processing model %s" % basename(file))
		try:
			# preprocess model
			preprocess()
			# translate
			translate()
		except Exception:
			print("failed to process model %s" % basename(file))
			print(traceback.format_exc())

if __name__ == '__main__':
	args = []
	for i in range(1,len(sys.argv)):
		args.append(sys.argv[i])
	main(args)

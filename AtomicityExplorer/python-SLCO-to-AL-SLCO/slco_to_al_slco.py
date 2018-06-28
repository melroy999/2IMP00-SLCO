# Race Condition Explorer tool, v0.1, 2017
#
# Update History:
#

# Start of program

import argparse
import logging
import logging.config
import sys
from os.path import dirname, join
import jinja2
from textx.metamodel import metamodel_from_file
from textx.model import children_of_type

from help_on_error_argument_parser import HelpOnErrorArgumentParser
from suggestions import *

this_folder = dirname(__file__)

# import SLCO library
sys.path.append(join(this_folder,'../../libraries'))
from slcolib import *

# set of actions in the model
actions = set([])

# dictionaries providing for each state machine in the model the number of newly introduced local variables of a specific type
nr_local_int_vars = {}
nr_local_byte_vars = {}
nr_local_bool_vars = {}

# *** BEGIN TRANSLATION FILTERS ***

def printstatement(s):
	"""print the given statement"""
	result = ''
	if s.__class__.__name__ == "Assignment":
		result += s.left.var.name
		if s.left.index != None:
			result += "[" + printstatement(s.left.index) + "]"
		result += " := " + printstatement(s.right)
	elif s.__class__.__name__ == "Composite":
		result += "["
		if s.guard != None:
			result += printstatement(s.guard)
			if len(s.assignments) > 1:
				result += ";"
		for i in range(0,len(s.assignments)):
			result += " " + printstatement(s.assignments[i])
			if i < len(s.assignments)-1:
				result += ";"
		result += "]"
	elif s.__class__.__name__ == "ReceiveSignal":
		result += "receive " + s.signal + '('
		first = True
		for p in s.params:
			if not first:
				result += ', '
			else:
				first = False
			result += printstatement(p)
		if s.guard != None:
			result += " | " + printstatement(s.guard)
		result += ") from " + s.target.name
	elif s.__class__.__name__ == "SendSignal":
		result += "send " + s.signal + '('
		first = True
		for p in s.params:
			if not first:
				result += ', '
			else:
				first = False
			result += printstatement(p)
		result += ") to " + s.target.name
	elif s.__class__.__name__ == "Delay":
		result += "after " + str(s.length) + " ms"
	elif s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2" or s.__class__.__name__ == "ExprPrec1":
		if s.op != '':
			result += printstatement(s.left) + " " + s.op + " " + printstatement(s.right)
		else:
			result += printstatement(s.left)
	elif s.__class__.__name__ == "Primary":
		result += s.sign
		if s.sign == "not":
			result += " "
		if s.value != None:
			newvalue = s.value
			result += str(newvalue).lower()
		elif s.ref != None:
			result += s.ref.ref
			if s.ref.index != None:
				result += "[" + printstatement(s.ref.index) + "]"
		else:
			result += '(' + printstatement(s.body) + ')'
	elif s.__class__.__name__ == "VariableRef":
		result += s.var.name
		if s.index != None:
			result += "[" + printstatement(s.index) + "]"
	return result

def variabledeclarations(s, indent):
	"""provide list of variable declarations for given array of variables"""
	previous_base = ""
	previous_size = 0
	output = ""
	if len(s) > 0:
		output = "variables"
	for i in range(0,len(s)):
		# write type?
		if s[i].type.base != previous_base or s[i].type.size != previous_size:
			output += "\n  "
			for j in range (0,indent):
				output += " "
			output += s[i].type.base
			if s[i].type.size > 1:
				output += "[" + str(s[i].type.size) + "]"
			previous_base = s[i].type.base
			previous_size = s[i].type.size
		output += " " + s[i].name
		# add default value?
		if s[i].defvalue != None or s[i].defvalues != []:
			output += " := "
			if s[i].defvalue != None:
				output += str(s[i].defvalue)
			else:
				output += str(s[i].defvalues)
	if output != "":
		for i in range (0,indent):
			output += " "
	return output

# *** END TRANSLATION FILTERS ***

def apply_suggestions(model, suggestions):
	global nr_local_int_vars, nr_local_byte_vars, nr_local_bool_vars

	for o in model.objects:
		for sm in o.type.statemachines:
			for tr in sm.transitions:
				# process suggestions
				ad = suggestions.get(tuple([o.name, sm.name, "ST'" + str(tr._tx_position)]), None)
				if ad: # atomicity violations, apply advice
					break_down_statements(tr, sm, o)
				else: # no atomicity violations. If the statement is composite, remove the composite aspect from the model
					newst = []
					for st in tr.statements:
						if st.__class__.__name__ == "Composite":
							if st.guard != None:
								newst.append(st.guard)
							for stt in st.assignments:
								newst.append(stt)
						else:
							newst.append(st)
					tr.statements = newst
			#composites = children_of_type("Composite", t)
			# We assume that a transition only contains one statement.
			# Hence, we can simply assign the new statements
			#if composites:
			#	composite = composites[0]
			#	t.statements = ad.apply(composite)
	
	# We do not support actions
	#model.actions
	# We do not support multiple objects
	#model.objects
	# We do not support channels
	#model.channels
	#globalClass.ports
	return model

def expression(s,primmap):
	"""Rewrites given expression s according to given variable dictionary primmap."""
	output = ''
	# special case: s is a variableref. In this case, it is the left-hand side of an assignment, and s refers to an array
	if s.__class__.__name__ == "Variable":
		output = primmap.get(tuple([s.name]), s)
	if s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2" or s.__class__.__name__ == "ExprPrec1":
		sc = copy.deepcopy(s)
		sc.left = expression(s.left, primmap)
		sc.right = expression(s.right, primmap)
		output = sc
	elif s.__class__.__name__ == "Primary":
		if s.value != None:
			output = s
		elif s.ref != None:
			if s.ref.ref in actions:
				output = s
			else:
				sc = copy.deepcopy(s)
				# is an index to an array given?
				if s.ref.index != None:
					varname = s.ref.ref
					varname_with_index = varname + "[" + expression(s.ref.index,primmap)
					if primmap.get(varname_with_index) != None:
						sc.ref.index = primmap.get(varname_with_index)
				output = primmap.get(tuple([s.ref.ref, sc.ref.index]), s)
		else:
			output = expression(s.body,primmap)
	return output

def create_var(sm, v, type):
	"""Create and return a variable object for the variable named v of given type, associated to the given state machine sm"""
	newv = Variable(sm, '', v, '', [])
	if type == "Boolean":
		t = Type(newv, 'Boolean', 1)
	elif type == "Byte":
		t = Type(newv, 'Byte', 1)
	else:
		t = Type(newv, 'Boolean', 1)
	newv.type = t
	return newv

def create_var_expression(st, v, i):
	"""Create and return a new expression containing only a reference to the given variable name (with possibly index i). Associate the expression with the given statement st"""
	e = Expression(st, '', '', '')
	e4 = ExprPrec4(e, '', '', '')
	e3 = ExprPrec3(e4, '', '', '')
	e2 = ExprPrec2(e3, '', '', '')
	e1 = ExprPrec1(e2, '', '', '')
	p = Primary(e1, '', '', '', '')
	r = ExpressionRef(p, v, '')
	e.left = e4
	e4.left = e3
	e3.left = e2
	e2.left = e1
	e1.left = p
	p.ref = r
	return e

def break_down_statements(tr, sm, o):
	"""Break down the statements of the given transition tr. Involves transforming those statements into a new statement block,
	in which each statement only accesses a single global variable, and at most once (read or write).
	sm and o are the owning state machine and object, respectively"""
	global nr_local_int_vars, nr_local_byte_vars, nr_local_bool_vars

	livarcount = 0
	lbvarcount = 0
	lbyvarcount = 0
	# build vardict for the use of local variables
	vardict = {}
	for s in tr.statements:
		vars = statement_varset(s)
		for v in vars:
			if vardict.get(v) == None:
				# lookup referenced variable to figure out type
				tt = ''
				for v2 in o.type.variables:
					if v2.name == v:
						tt = v2.type
						break
				# if we have not found a type, the variable is state machine-local, therefore not relevant
				if tt == 'Integer':
					vardict[v] = "itmp'" + str(livarcount)
					livarcount += 1
				elif tt == 'Boolean':
					vardict[v] = "btmp'" + str(lbvarcount)
					lbvarcount += 1
				elif tt == 'Byte':
					vardict[v] = "bytmp'" + str(lbyvarcount)
					lbyvarcount += 1
	# now that we have assigned local vars to global vars, create new block of statements
	newstat = []
	for s in tr.statements:
		if s.guard != None:
			vars = statement_varset(s.guard)
			for v in vars:
				ns = Assignment(tr, )

def statement_varset(s):
	"""Produces two sets of variables referenced in given SLCO statement, the first for read accesses and the second for write accesses"""
	global actions
	outputread = set([])
	outputwrite = set([])
	if s.__class__.__name__ == "Assignment":
		outputwrite |= statement_varset(s.left)
		outputread |= statement_varset(s.right)
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			outputread |= statement_varset(s.guard)
		for a in s.assignments:
			outputwrite = statement_varset(a.left)
			outputread |= statement_varset(a.right)
	elif s.__class__.__name__ == "ReceiveSignal":
		for p in s.params:
			outputwrite |= statement_varset(p)
		if s.guard != None:
			outputread |= statement_varset(s.guard)
	elif s.__class__.__name__ == "SendSignal":
		for p in s.params:
			outputread |= statement_varset(p)
	elif s.__class__.__name__ == "VariableRef":
		output.add(s.var.name)
		if s.index != None:
			output |= statement_varset(s.index)
	elif s.__class__.__name__ == "Delay":
		output |= set([])
	elif s.__class__.__name__ != "Primary":
		output |= statement_varset(s.left)
		if s.op != '':
			output |= statement_varset(s.right)
	else:
		if s.ref != None:
			if s.ref.ref not in actions:
				output.add(s.ref.ref)
	return output

#def combine_varsets(O,N):
#	"""Combine two lists of varsets"""
#	return [O[0] | N[0], O[1] | N[1]]
#
#def statement_varsets(s):
#	"""Produces sets of variables referenced in given SLCO statement, one for read accesses, one for write accesses"""
#	global actions
#	output = [set([]), set([])]
#	if s.__class__.__name__ == "Assignment":
#		output = combine_varsets(output, statement_varsets(s.left))
#		output = combine_varsets(output, statement_varsets(s.right))
#	elif s.__class__.__name__ == "Composite":
#		if s.guard != None:
#			output = combine_varsets(output, statement_varsets(s.guard))
#		for a in s.assignments:
#			output = combine_varsets(output, statement_varsets(a))
#	elif s.__class__.__name__ == "ReceiveSignal":
#		for p in s.params:
#			output = combine_varsets(output, statement_varsets(p))
#		if s.guard != None:
#			output = combine_varsets(output, statement_varsets(s.guard))
#	elif s.__class__.__name__ == "SendSignal":
#		for p in s.params:
#			output = combine_varsets(output, statement_varsets(p))
#	elif s.__class__.__name__ == "VariableRef":
#		# VariableRefs always indicate write accesses
#		output[1].add(s.var.name)
#		if s.index != None:
#			output = combine_varsets(output, statement_varsets(s.index))
#	elif s.__class__.__name__ == "Delay":
#		output |= [set([]), set([])]
#	elif s.__class__.__name__ != "Primary":
#		output = combine_varsets(output, statement_varsets(s.left))
#		if s.op != '':
#			output = combine_varsets(output, statement_varsets(s.right))
#	else:
#		if s.ref != None:
#			if s.ref.ref not in actions:
#				output[0].add(s.ref.ref)
#	return output

def translate(model, suggestions, path):
	"""The translation function"""
	
	# Initialize the template engine.
	jinja_env = jinja2.Environment(loader=jinja2.FileSystemLoader(join(this_folder,'../../jinja2_templates')), trim_blocks=True, lstrip_blocks=True, extensions=['jinja2.ext.loopcontrols','jinja2.ext.do',])

	# Register the filters
	jinja_env.filters['printstatement'] = printstatement
	jinja_env.filters['variabledeclarations'] = variabledeclarations
	
	# Register the tests

	# apply selected transformations
	model = apply_suggestions(model, suggestions)
	# load the SLCO template
	template = jinja_env.get_template('slco.jinja2template')
	out = template.render(model=model)
	# write new SLCO model
	outFile = open(path, 'w')
	outFile.write(out)
	outFile.close()

def main():
	global actions

	# setup logging
	file_handler    = logging.FileHandler(filename='slco_to_al_slco.log', mode='w')
	console_handler = logging.StreamHandler(stream=sys.stdout)
	file_handler.setLevel(logging.INFO)
	console_handler.setLevel(logging.DEBUG)
	logging.basicConfig(format='%(asctime)s - %(levelname)s: %(message)s',
						datefmt='%Y-%m-%d %H:%M:%S',
						level=logging.DEBUG,
						handlers=[file_handler, console_handler])
	
	# parse arguments
	parser = HelpOnErrorArgumentParser(
		description='Core-SLCO to Atomicity-Level-SLCO transformation',
		formatter_class=argparse.ArgumentDefaultsHelpFormatter
	)
	parser.add_argument("INPUT_MODEL", type=str, help="SLCO input model")
	parser.add_argument("INPUT_SUGGESTIONS", type=str, help="Suggestions file generated by mCRL2 analysis")
	parser.add_argument("-o", "--out", type=str, default="INPUT_MODEL", help="Output AL-SLCO model")
	parser.add_argument("-q", "--quiet", action='store_true', help="Quiet mode, print no messages to screen")
	parser.add_argument("-m", "--mute", action='store_true', help="Mute mode, no messages are printed or logged")
	
	args = vars(parser.parse_args())
	# set options
	if args['quiet']:
		console_handler.setLevel(logging.CRITICAL + 1)

	if args['mute']:
		console_handler.setLevel(logging.CRITICAL + 1)
		file_handler.setLevel(logging.CRITICAL + 1)
	
	slco_path = args['INPUT_MODEL']
	sugg_path = args['INPUT_SUGGESTIONS']
	
	out_path = args['out']
	if out_path == 'INPUT_MODEL':
		out_path = slco_path[:-5] + '.alslco'
	elif not out_path.endswith('.alslco'):
		out_path = out_path + '.alslco'
	
	logging.info('Starting SLCO Atomicity-Level model transformation')
	logging.info('Input model       : %s', slco_path)
	logging.info('Input suggestions : %s', sugg_path)
	logging.info('Output File       : %s', out_path)

	# read model
	model = read_SLCO_model(slco_path)
	# build set of actions in model
	for a in model.actions:
		actions.add(a)
	suggestions = parse_suggestions(sugg_path)
	# translate
	out_model = translate(model, suggestions, out_path)
	
	logging.info('Finished, output written to %s', out_path)
	logging.shutdown()


if __name__ == '__main__':
	main()

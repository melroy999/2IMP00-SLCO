# SLCO 2.0 to multi-threaded Java transformation, limited to SLCO models consisting of a single object

import sys
import os
import jinja2
from textx.metamodel import metamodel_from_file
import re

# Set of all state names in the model
states = set([])
# number of elementary global variables in the model
numberofelemvariables = 0
# names of state machine local variables
smlocalvars = set([])
# dictionary providing lock ids (offset) for a given variable
varids = {}

this_folder = os.path.dirname(__file__)

def operator(s):
	"""Provide characters to display given operator s"""
	if s == '>':
		return '>'
	elif s == '<':
		return '<'
	elif s == '>=':
		return '>='
	elif s == '<=':
		return '<='
	elif s == '=':
		return '=='
	elif s == '!=':
		return '!='
	elif s == 'and':
		return '&&'
	elif s == 'or':
		return '||'
	elif s == '<>':
		return '!='
	else:
		return s

def sign(s):
	if s == 'not':
		return '!'
	else:
		return s

def getlabel(s):
	"""Get the label for the given statement s"""
	result = ''
	if s.__class__.__name__ == "Assignment":
		result += s.left.var.name
		if s.left.index != None:
			result += "[" + getlabel(s.left.index) + "]"
		result += " := " + getlabel(s.right)
	elif s.__class__.__name__ == "Composite":
		result += "["
		if s.guard != None:
			result += getlabel(s.guard)
			result += ";"
		for i in range(0,len(s.assignments)):
			result += " " + getlabel(s.assignments[i])
			if i < len(s.assignments)-1:
				result += ";"
		result += "]"
	elif s.__class__.__name__ == "Delay":
		result += "<b>after </b>" + str(s.length) + "<b> ms</b>"
	elif s.__class__.__name__ == "SendSignal":
		result += "<b>send </b>" + s.signal + "("
		first = True
		for p in s.params:
			if not first:
				result += ","
			else:
				first = False
			result += getlabel(p)
		result += ") <b>to </b>" + s.target.name
	elif s.__class__.__name__ == "ReceiveSignal":
		result += "<b>receive </b>" + s.signal + "("
		first = True
		for p in s.params:
			if not first:
				result += ","
			else:
				first = False
			result += getlabel(p)
		if s.guard != None:
			result += " | " + getlabel(s.guard)
		result += ") <b>from </b>" + s.target.name
	elif s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2" or s.__class__.__name__ == "ExprPrec1":
		if s.op != '':
			result += getlabel(s.left) + " " + operator(s.op) + " " + getlabel(s.right)
		else:
			result += getlabel(s.left)
	elif s.__class__.__name__ == "Primary":
		result += s.sign
		if s.sign == "not":
			result += " "
		if s.value != None:
			newvalue = s.value
			result += str(newvalue)
		elif s.ref != None:
			result += s.ref.ref
			if s.ref.index != None:
				result += "[" + getlabel(s.ref.index) + "]"
		else:
			result += '(' + getlabel(s.body) + ')'
	elif s.__class__.__name__ == "VariableRef":
		result += s.var.name
		if s.index != None:
			result += "[" + getlabel(s.index) + "]"
	return result

def getinstruction(s):
	"""Get the Java instruction for the given statement s"""
	global smlocalvars
	result = ''
	if s.__class__.__name__ == "Assignment":
		result += s.left.var.name
		if s.left.index != None:
			result += "[" + getinstruction(s.left.index) + "]"
		result += " = " + getinstruction(s.right)
	elif s.__class__.__name__ == "Composite":
		result += "["
		if s.guard != None:
			result += getinstruction(s.guard)
		if len(s.assignments) > 1:
			result += ";"
		for i in range(0,len(s.assignments)):
			result += " " + getinstruction(s.assignments[i])
			if i < len(s.assignments)-1:
				result += ";"
		result += "]"
	elif s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2" or s.__class__.__name__ == "ExprPrec1":
		if s.op != '':
			result += getinstruction(s.left) + " " + operator(s.op) + " " + getinstruction(s.right)
		else:
			result += getinstruction(s.left)
	elif s.__class__.__name__ == "Primary":
		result += sign(s.sign)
		if s.sign == "not":
			result += "("
		if s.value != None:
			newvalue = s.value
			result += str(newvalue).lower()
		elif s.ref != None:
			result += s.ref.ref
			if s.ref.index != None:
				result += "[" + getinstruction(s.ref.index) + "]"
		else:
			result += '(' + getinstruction(s.body) + ')'
		if s.sign == "not":
			result += ")"
	elif s.__class__.__name__ == "VariableRef":
		result += s.var.name
		if s.index != None:
			result += "[" + getinstruction(s.index) + "]"
	return result

def javatype(s):
	"""Maps type names from SLCO to Java"""
	if s.base == 'Integer':
		if s.size < 2:
			return 'int'
		else:
			return 'int[]'
	elif s.base == 'Boolean':
		if s.size < 2:
			return 'boolean'
		else:
			return 'boolean[]'
	elif s.base == 'Byte':
		if s.size < 2:
			return 'byte'
		else:
			return 'byte[]'

def javastatement(s,nlocks,indent,nondet):
	"""Translates SLCO statement s to Java code. indent indicates how much every line needs to be indented, nlocks indicates how many locks need to be acquired (optional). nondet indicates whether this statement is at the head of a statement block and in a non-deterministic choice; it affects how expressions are translated."""
	output = ""
	if s.__class__.__name__ == "Assignment":
		output += getinstruction(s) + ";"
	elif s.__class__.__name__ == "Expression":
		if not nondet:
			output += "while(!(" + getinstruction(s) + ")) { kp.unlock(lockIDs, "
			output += str(nlocks)
			output += "); try{ wait(100); } catch (InterruptedException e) { break; } kp.lock(lockIDs, "
			output += str(nlocks) + ");}"
		else:
			output += "if (!(" + getinstruction(s) + ")) { kp.unlock(lockIDs, "
			output += str(nlocks)
			output += "); transcounter++; break; }"
	elif s.__class__.__name__ == "Composite":
		indentspace = ""
		for i in range(0,indent):
			indentspace += " "
		if s.guard != None:
			output += javastatement(s.guard,nlocks,indent,nondet)
		if len(s.assignments) > 0:
			output += "\n"
		first = True
		for e in s.assignments:
			if not first:
				output += "\n"
			else:
				first = False
			output += indentspace + getinstruction(e) + ";"
	return output

def expression(s,primmap):
	"""Maps SLCO expression to mCRL2 expression. Primmap is a dictionary for rewriting primaries."""
	output = ''
	# special case: s is a variableref. In this case, it is the left-hand side of an assignment, and s refers to an array
	if s.__class__.__name__ == "Variable":
		output = primmap.get(s.name, s.name)
	if s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2":
		#if s.op != '':
		#	output = '('
		if s.op != '' and s.op != 'xor':
			output += expression(s.left,primmap) + " " + operator(s.op) + " " + expression(s.right,primmap)
		elif s.op == 'xor':
			output += operator(s.op) + '(' + expression(s.left,primmap) + ', ' + expression(s.right,primmap) + ')'
		else:
			output += expression(s.left,primmap)
	elif s.__class__.__name__ == "ExprPrec1":
		if s.op != '':
			output += operator(s.op) + '(' + expression(s.left,primmap) + ', ' + expression(s.right,primmap) + ')'
		else:
			output += expression(s.left,primmap)
	elif s.__class__.__name__ == "Primary":
		output = operator(s.sign)
		if s.value != None:
			newvalue = s.value
			output += str(newvalue).lower()
		elif s.ref != None:
			# is an index to an array given?
			key = s.ref.ref
			if s.ref.index != None:
				key += "[" + expression(s.ref.index,primmap) + "]"
			output += primmap.get(key, key)
		else:
			output += '(' + expression(s.body,primmap) + ')'
	return output

def statementvarids(s,primmap):
	"""Produce for the given statement a list of sorted lock ids to be acquired"""
	global varids
	output = []
	if s.__class__.__name__ == "VariableRef":
		# is the variable not local to state machine?
		if varids.get(s.var.name) != None:
			varid = varids[s.var.name]
			if s.index != None:
				varid += " + " + expression(s.index,primmap)
			output.append(varid)
	elif s.__class__.__name__ == "Composite":
		# update primmap
		if s.guard != None:
			output += statementvarids(s.guard,primmap)
		for e in s.assignments:
			output += statementvarids(e.left,primmap)
			output += statementvarids(e.right,primmap)
			newright = expression(e.right,primmap)
			varname = e.left.var.name
			if e.left.index != None:
				varname += "[" + expression(e.left.index,primmap) + "]"
			primmap[varname] = "(" + newright + ")"
	elif s.__class__.__name__ == "Assignment":
		output += statementvarids(s.left,primmap)
		output += statementvarids(s.right,primmap)
	elif s.__class__.__name__ != "Primary":
		output += statementvarids(s.left,primmap)
		if s.op != '':
			output += statementvarids(s.right,primmap)
	else:
		if s.ref != None:
			# IGNORE STATE MACHINE LOCAL VARS!
			if varids.get(s.ref.ref) != None:
				varid = varids[s.ref.ref]
				if s.ref.index != None:
					varid += " + " + expression(s.ref.index,primmap)
				output.append(varid)
	# remove duplicates
	output = list(set(output))
	# sort output
	sortedoutput = sorted(output)
	return sortedoutput

def getvarids(s):
	return statementvarids(s,{})

def maxnumbervarids(s):
	"""For the given state machine s, determine max number of varids required for a statement contained in it"""
	maxnumber = 0
	for tr in s.transitions:
		for st in tr.statements:
			varids = statementvarids(st,{})
			if len(varids) > maxnumber:
				maxnumber = len(varids)
	return maxnumber

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
			defv += v
		defv += ']'
		return defv
	elif s.type.base == 'Integer' or s.type.base == 'Byte':
		if s.type.size < 2:
			return '0'
		else:
			type = '{'
			first = True
			for i in range(0,s.type.size):
				if not first:
					type += ','
				else:
					first = False
				type += '0'
			type += '}'
			return type
	elif s.type.base == 'Boolean':
		if s.type.size < 2:
			return 'true'
		else:
			type = '{'
			first = True
			for i in range(0,s.type.size):
				if not first:
					type += ','
				else:
					first = False
				type += 'true'
			type += '}'
			return type

def initialvalue(s,o):
	""" return initial value for given global variable in given object o """
	# try to find variable in initial assignments
	value = ''
	values = []
	for vinit in o.assignments:
		if s.name == vinit.left.name:
			if vinit.right != None:
				value = getinstruction(vinit.right)
			else:
				for v in vinit.rights:
					values.append(str(v).lower())
	if value != '':
		return value
	elif values != []:
		output = '{'
		first = True
		for v in values:
			if not first:
				output += ','
			else:
				first = False
			output += v
		output += "}"
		return output
	elif s.defvalue != None:
		return s.defvalue
	elif s.defvalues != []:
		defv = '{'
		first = True
		for v in s.defvalues:
			if not first:
				defv += ','
			else:
				first = False
			defv += str(v)
		defv += '}'
		return defv
	elif s.type.base == 'Integer' or s.type.base == 'Byte':
		if s.type.size < 2:
			return '0'
		else:
			type = '{'
			first = True
			for i in range(0,s.type.size):
				if not first:
					type += ','
				else:
					first = False
				type += '0'
			type += '}'
			return type
	elif s.type.base == 'Boolean':
		if s.type.size < 2:
			return 'true'
		else:
			type = '{'
			first = True
			for i in range(0,s.type.size):
				if not first:
					type += ','
				else:
					first = False
				type += 'true'
			type += '}'
			return type

def outgoingtrans(s,t):
	"""Return the set of transitions with s as source"""
	tlist = []
	for tr in t:
		if tr.source.name == s.name:
			tlist.append(tr)
	return tlist

def hasoutgoingtrans(s,t):
	"""Check whether state s has outgoing transitions in t"""
	for tr in t:
		if tr.source.name == s.name:
			return True
	return False

def preprocess(model):
	"""Preprocess the model"""
	global states, numberofelemvariables, smlocalvars, varids
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
	# fill set of state names
	states  = set([])
	for c in model.classes:
		for sm in c.statemachines:
			for s in sm.states:
				states.add(s.name)
	# compute number of elementary variables
	numberofelemvariables = 0
	for c in model.classes:
		for v in c.variables:
			if v.type.size > 1:
				numberofelemvariables += v.type.size
			else:
				numberofelemvariables += 1
	# build set of state machine local variable names
	smlocalvars = set([])
	for c in model.classes:
		for sm in c.statemachines:
			for v in sm.variables:
				smlocalvars.add(v.name)
	# build dictionary of global variables with ids
	varids = {}
	# first create list of global variables and sort it
	varlist = []
	for c in model.classes:
		for v in c.variables:
			varlist.append(v)
	sortedlist = sorted(varlist, key=lambda v: v.name)
	# create dict
	count = 0
	for v in sortedlist:
		varids[v.name] = str(count)
		if v.type.size > 1:
			count += v.type.size
		else:
			count += 1
	return model

lockscanner=re.Scanner([
	(r"[A-Za-z0-9]+:",											lambda scanner,token:("OBJECT", token)),
	(r"var_[A-Za-z0-9]+(\([0-9]+\))?",			lambda scanner,token:("VARIABLE", token)),
	(r"[\s\(\),]+", None), # None == skip token.
])

def read_locking_file(model,lockingfilename):
	"""Read locking file and return dict of vars to lock"""
	global varids
	lockdict = {}
	if lockingfilename != '':
		try:
			inFile = open(lockingfilename,'r')
		except IOError:
			print("ERROR: locking file does not exist!")
			exit(1);
		inFile.close()
		key = ''
		for line in open(lockingfilename):
			remainder = line
			while remainder != "":
				results, remainder = lockscanner.scan(remainder)
			if results[0][0] == 'OBJECT':
				key = results[0][1][:-1]
			else:
				varlist = []
				for i in range(0,len(results)):
					if results[i][0] == 'VARIABLE':
						varlist.append(results[i][1][4:])
				oldlist = lockdict.get(key,[])
				varlist += oldlist
				lockdict[key] = varlist
	else:
		# fill lockdict with all variables in the system
		for o in model.objects:
			varlist = []
			for v in o.type.variables:
				varname = v.name
				if v.type.size > 1:
					for i in range(0,v.type.size):
						varlist.append(varname + "(" + str(i) + ")")
				else:
					varlist.append(varname)
			lockdict[o.name] = varlist
	return lockdict

def slco_to_java(modelfolder,modelname,model,lockingdict):
	"""The translation function"""
	global states, varids, numberofelemvariables
	outFile = open(os.path.join(modelfolder,modelname[:-4] + "java"), 'w')

	# prepare lockingdict information for code generator
	lockids = []
	for o in model.objects:
		locklist = lockingdict.get(o.name,[])
		for v in locklist:
			vsplit = v.split('(')
			vid = int(varids.get(vsplit[0],"0"))
			if len(vsplit) > 1:
				vx = vsplit[1].rstrip(')')
				vid = vid + int(vx)
			lockids.append(vid)
	lockids = set(lockids)
	lockneeded = []
	for i in range(0,numberofelemvariables):
		lockneeded.append(i in lockids)

	# Initialize the template engine.
	jinja_env = jinja2.Environment(loader=jinja2.FileSystemLoader(this_folder), trim_blocks=True, lstrip_blocks=True, extensions=['jinja2.ext.loopcontrols','jinja2.ext.do',])

	# Register the filters
	jinja_env.filters['getvarids'] = getvarids
	jinja_env.filters['maxnumbervarids'] = maxnumbervarids
	jinja_env.filters['getlabel'] = getlabel
	jinja_env.filters['variabledefault'] = variabledefault
	jinja_env.filters['initialvalue'] = initialvalue
	jinja_env.filters['javatype'] = javatype
	jinja_env.filters['outgoingtrans'] = outgoingtrans
	jinja_env.filters['javastatement'] = javastatement

	# Register the tests
	jinja_env.tests['hasoutgoingtrans'] = hasoutgoingtrans

	# load the Java template
	template = jinja_env.get_template('java.jinja2template')

	# write the program
	outFile.write(template.render(model=model,states=states,numberofelemvariables=numberofelemvariables,lockneeded=lockneeded))
	outFile.close()

def main(args):
	"""The main function"""
	global numberofelemvariables
	lockingfilename = ''
	if len(args) == 0:
		print("Missing argument: SLCO model")
		sys.exit(1)
	else:
		if args[0] == '-h' or args[0] == '-help':
			print("Usage: pypy/python3 slco2java")
			print("")
			print("Transform an SLCO 2.0 model to a Java program.")
			print("-l <file>							provide locking file for smart locking")
			sys.exit(0)
		else:
			i = 0
			while i < len(args):
				if args[i] == '-l':
					i += 1
					if i >= len(args):
						print("ERROR: lock file name missing!")
						exit(1);
					lockingfilename = args[i];
				else:
					modelfolder, modelname = os.path.split(args[i])
				i += 1

	# create meta-model
	slco_mm = metamodel_from_file(os.path.join(this_folder,'slco2.tx'))
	# read model
	model = slco_mm.model_from_file(os.path.join(modelfolder,modelname))
	# preprocess
	model = preprocess(model)
	# read locking file
	lockingdict = read_locking_file(model,lockingfilename)
	# translate
	slco_to_java(modelfolder,modelname,model,lockingdict)

	for o in model.objects:
		lockedvars = lockingdict.get(o.name,[])
		lockedvars = set(lockedvars)
	print("SLCO model translated to Java")
	print("Ratio of locked variables/total number: " + str(len(lockedvars)) + "/" + str(numberofelemvariables))

if __name__ == '__main__':
	args = []
	for i in range(1,len(sys.argv)):
		args.append(sys.argv[i])
	main(args)

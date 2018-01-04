import sys
from os import mkdir
from os.path import exists, dirname, basename, join, split
import jinja2
from textx.metamodel import metamodel_from_file
from copy import deepcopy, copy
import itertools
import glob
import traceback

modelname = ""
model = ""
this_folder = dirname(__file__)

check_variables = False
check_sequences = False

# set of actions in model
actions = set([])
# dictionary to look up state machine owning a given statement
statemachine = {}
# dictionary to look up transition owning a given statement
tr = {}

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
			result += "("
		if s.value != None:
			newvalue = s.value
			result += str(newvalue).lower()
		elif s.ref != None:
			result += s.ref.ref
			if s.ref.index != None:
				result += "[" + printstatement(s.ref.index) + "]"
		else:
			result += '(' + printstatement(s.body) + ')'
		if s.sign == "not":
			result += ")"
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
			output += " " + s[i].type.base
			if s[i].type.size > 1:
				output += "[" + str(s[i].type.size) + "]"
			previous_base = s[i].type.base
			previous_size = s[i].type.size
		output += " " + s[i].name
		# add default value?
		if s[i].defvalue != None or s[i].defvalues != []:
			output += " := "
			if s[i].defvalue != None:
				output += s[i].defvalue
			else:
				output += s[i].defvalues
	if output != "":
		output += "\n"
		for i in range (0,indent):
			output += " "
	return output

# *** END TRANSLATION FILTERS ***

# *** BEGIN TRANSLATION TESTS ***

# *** END TRANSLATION TESTS ***

def statement_varset(s):
	"""Produces set of variables referenced in given SLCO statement"""
	global actions
	output = set([])
	if s.__class__.__name__ == "Assignment":
		output.add(s.left.var.name)
		output |= statement_varset(s.right)
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			output |= statement_varset(s.guard)
		for a in s.assignments:
			output |= statement_varset(a)
	elif s.__class__.__name__ == "ReceiveSignal":
		for p in s.params:
			output |= statement_varset(p)
		if s.guard != None:
			output |= statement_varset(s.guard)
	elif s.__class__.__name__ == "SendSignal":
		for p in s.params:
			output |= statement_varset(p)
	elif s.__class__.__name__ == "VariableRef":
		output.add(s.var.name)
		if s.index != None:
			output |= statement_varset(s.index)
	elif s.__class__.__name__ == "Delay":
		output = set([])
	elif s.__class__.__name__ != "Primary":
		output |= statement_varset(s.left)
		if s.op != '':
			output |= statement_varset(s.right)
	else:
		if s.ref != None:
			if s.ref.ref not in actions:
				output.add(s.ref.ref)
	return output

def check_vars(m):
	"""check the use of variables in the model, and improve where needed"""
	# build a dictionary providing sets of state machine-local variables
	smvars = {}
	for c in model.classes:
		smvars[c] = {}
		for sm in c.statemachines:
			smvars[c][sm] = set([])
			for v in sm.variables:
				smvars[c][sm].add(v.name)
	# keep track of state machines referencing class variables, and if state machine-local variables are referenced
	classvars_references = {}
	smvars_referenced = {}
	for c in model.classes:
		smvars_referenced[c] = {}
		classvars_references[c] = {}
		for sm in c.statemachines:
			smvars_referenced[c][sm] = set([])
			varset = set([])
			for tr in sm.transitions:
				for stat in tr.statements:
					varset |= statement_varset(stat)
			# process varset
			for v in varset:
				# if the variable is state machine-local, add it to smvars_referenced, otherwise add a reference to classvars_references
				if v in smvars[c][sm]:
					smvars_referenced[c][sm].add(v)
				else:
					smset = classvars_references[c].get(v,set([]))
					smset.add(sm)
					classvars_references[c][v] = smset
	# change model to take result into account
	# remove variables that are not referenced at all
	for c in m.classes:
		newvars = []
		newsmvars = {}
		for v in c.variables:
			refset = classvars_references[c].get(v.name,set([]))
			if len(refset) < 2:
				# changes need to be applied
				if len(refset) == 1:
					# move variable to var list of state machine referencing the variable
					sm = refset.pop()
					varset = newsmvars.get(sm,set([]))
					varset.add(v)
					newsmvars[sm] = varset
			else:
				# keep variable in list
				newvars.append(v)
		# set new variable list
		c.variables = newvars
		for sm in c.statemachines:
			newvars = []
			for v in sm.variables:
				if v in smvars_referenced[c][sm]:
					newvars.append(v)
			for v in newsmvars.get(sm,set([])):
				newvars.append(v)
			sm.variables = newvars

def statement_is_blocking(s):
	"""Is the given statement blocking or not?"""
	if s.__class__.__name__ == "Assignment":
		return False
	elif s.__class__.__name__ == "Composite":
		if s.guard == None:
			return False
		else:
			return True
	else:
		return True

def combine_trans(m):
	"""Combine transitions, i.e., statements associated with them, that are placed in sequence without any transitions branching off"""
	"""Also make sure no blocking statements appear in the middle or end of a statement block"""
	# first add additional states and transitions to remove blocking statements from blocks
	for c in m.classes:
		for sm in c.statemachines:
			newstatecount = 0
			for tr in sm.transitions:
				first = True
				newblocks = []
				newblock = []
				for stat in tr.statements:
					if not first:
						if statement_is_blocking(stat):
							newblocks.append(newblock)
							newblock = [stat]
					else:
						newblock.append(stat)
						first = False
				newblocks.append(newblock)
				if len(newblocks) > 1:
					tr.statements = newblocks[0]
					tr1 = tr
					for i in range(1,len(newblocks)):
						tr2 = copy(tr1)
						# new state
						snew = copy(tr1.target)
						snew.name = "NewState" + str(newstatecount)
						newstatecount += 1
						sm.states.append(snew)
						tr2.target = tr1.target
						tr1.target = snew
						tr2.source = snew
						tr2.statements = newblocks[i]
						sm.transitions.append(tr2)
	# next, combine transitions where possible
	for c in m.classes:
		for sm in c.statemachines:
			trcount = {}
			transdict = {}
			singletransstateset = set([])
			# detect which states have a single, non-blocking outgoing transition
			for tr in sm.transitions:
				count = trcount.get(tr.source, 0)
				count += 1
				trcount[tr.source] = count
			# iterate again over the transitions, and store transition blocks linked to transitions that are the only transition of their source
			for tr in sm.transitions:
				if trcount[tr.source] == 1:
					if tr.statements == [] or not statement_is_blocking(tr.statements[0]):
						transdict[tr.source] = tr
						singletransstateset.add(tr.source)
			# combine transitions that have been selected as much as possible
			for s in singletransstateset:
				tr1 = transdict[s]
				while tr1.target in singletransstateset:
					tr1.statements += transdict[tr1.target].statements
					tr1.target = transdict[tr1.target].target
			# next, combine transitions
			for tr in sm.transitions:
				if tr.target in singletransstateset:
					tr.statements += transdict[tr.target].statements
					tr.target = transdict[tr.target].target
			# finally, remove selected states and transitions
			newstates = []
			for s in sm.states:
				if s not in singletransstateset or s == sm.initialstate:
					newstates.append(s)
			sm.states = newstates
			transtoremove = set([])
			for s, tr in transdict.items():
				transtoremove.add(tr)
			newtransitions = []
			for tr in sm.transitions:
				if tr not in transtoremove:
					newtransitions.append(tr)
			sm.transitions = newtransitions

	# for c in m.classes:
	# 	for sm in c.statemachines:
	# 		trcount = {}
	# 		transdict = {}
	# 		singletransstateset = set([])
	# 		for tr in sm.transitions:
	# 			count = trcount.get(tr.source, 0)
	# 			count += 1
	# 			trcount[tr.source] = count
	# 		# iterate again over the transitions, and store transition blocks linked to transitions that are the only transition of their source
	# 		for tr in sm.transitions:
	# 			if trcount[tr.source] == 1:
	# 				transdict[tr.source] = tr
	# 				singletransstateset.add(tr.source)
	# 		# combine transitions in the selected set, for as long as possible
	# 		updated = True
	# 		while updated:
	# 			updated = False
	# 			removestates = set([])
	# 			for s in singletransstateset:
	# 				if transdict[s].target in singletransstateset:
	# 					transdict[s].statements += transdict[transdict[s].target].statements
	# 					removestates.add(transdict[s].target)
	# 					transdict[s].target = transdict[transdict[s].target].target


def preprocess():
	"""preprocessing method"""
	global model, actions, statemachine, tr
	# build set of actions
	actions = set([])
	for a in model.actions:
		actions.add(a)
	# build dictionaries providing for a given statement the state machine and transition owning it
	for c in model.classes:
		for stm in c.statemachines:
			for trn in stm.transitions:
				for stat in trn.statements:
					statemachine[stat] = stm
					tr[stat] = trn
	# fill in types of variables
	for c in model.classes:
		for i in range(0,len(c.variables)):
			if c.variables[i].type == None:
				c.variables[i].type = c.variables[i-1].type
		for sm in c.statemachines:
			for i in range(0,len(sm.variables)):
				if sm.variables[i].type == None:
					sm.variables[i].type = sm.variables[i-1].type

def translate():
	"""The translation function"""
	global modelname, model, check_variables, check_sequences
	
	path, name = split(modelname)
	if name.endswith('.slco'):
		name = name[:-5]
	else:
		name = name[:-8]
	outFile = open(join(path,name + "_new.slco"), 'w')

	# Initialize the template engine.
	jinja_env = jinja2.Environment(loader=jinja2.FileSystemLoader(this_folder), trim_blocks=True, lstrip_blocks=True, extensions=['jinja2.ext.loopcontrols','jinja2.ext.do',])

	# Register the filters
	jinja_env.filters['printstatement'] = printstatement
	jinja_env.filters['variabledeclarations'] = variabledeclarations
	
	# Register the tests

	# apply selected transformations
	if check_variables:
		check_vars(model)
	if check_sequences:
		combine_trans(model)
	# load the SLCO template
	template = jinja_env.get_template('slco.jinja2template')
	out = template.render(model=model)
	# write new SLCO model
	outFile.write(out)
	outFile.close()

def main(args):
	"""The main function"""
	global modelname, model, check_variables, check_sequences
	if len(args) == 0:
		print("Missing argument: SLCO model")
		sys.exit(1)
	else:
		if args[0] == '-h' or args[0] == '-help':
			print("Usage: pypy/python3 slco2mcrl2 [-rc]")
			print("")
			print("Transform an SLCO 2.0 model to an SLCO 2.0 model.")
			print("")
			print(" -v                    transform use of variables; remove non-referenced ones and make variables that are not used by multiple state machines state machine-local")
			print(" -c                    combine transitions that model a sequence of statements")
			sys.exit(0)
		else:
			for i in range(0,len(args)):
				if args[i] == '-v':
					check_variables = True
				elif args[i] == '-c':
					check_sequences = True
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

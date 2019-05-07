import sys
from os import mkdir
from os.path import exists, dirname, basename, join, split
import jinja2
from textx.metamodel import metamodel_from_file
from copy import deepcopy, copy
import itertools
import glob
import traceback
import math

modelname = ""
model = ""
this_folder = dirname(__file__)

# import libraries
sys.path.append(join(this_folder,'../../libraries'))
from slcolib import *
from SCCTarjan import *
this_folder = dirname(__file__)

# state vector size
vectorsize = 0
# max state size
max_statesize = 0
# structure of vector
vectorstructure = []
vectorstructure_string = ""

# dictionary indicating in which part of the vector (which integer) a given vector element can be found
vectorelem_in_structure_map = {}
# state order: given a number, the name of the state can be retrieved
state_order = {}
# state id: given a state object, retrieve its order number in the list of states of that state machine
state_id = {}
# map smnames to smobjects
smname_to_object = {}

# set of statemachine names in the system
smnames = set([])

# LTL property
property_file = ""
# check for deadlocks?
deadlock_check = False

def cudatype(s, ignoresize):
	"""Maps type names from SLCO to CUDA"""
	if s.base == 'Integer':
		if s.size < 1 or ignoresize:
			return 'elem_inttype'
		else:
			return 'elem_inttype[]'
	elif s.base == 'Boolean':
		if s.size < 1 or ignoresize:
			return 'elem_chartype'
		else:
			return 'elem_chartype[]'
	elif s.base == 'Byte':
		if s.size < 1 or ignoresize:
			return 'elem_chartype'
		else:
			return 'elem_chartype[]'

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

def outgoingtrans(s,t):
	"""Return the set of transitions with s as source"""
	tlist = []
	for tr in t:
		if tr.source.name == s.name:
			tlist.append(tr)
	return tlist

def gettypesize(t):
	"""Return size of given type t"""
	add = 0
	if t.base == 'Integer':
		add = 32
	elif t.base == 'Boolean':
		add = 1
	else:
		add = 8
	L = []
	if t.size != None:
		for i in range(0,max(t.size,1)):
			L.append(add)
	else:
		L.append(add)
	return L

def scopename(v,o):
	"""Return full name of variable object o"""
	name = o.name
	if v.parent.__class__.__name__ == "StateMachine":
		name += "'" + v.parent.name
	name += "'" + v.name
	return name

def preprocess():
	"""Preprocessing of model"""
	global model, vectorsize, vectorstructure, vectorstructure_string, smnames, vectorelem_in_structure_map, max_statesize, state_order, smname_to_object, state_id

	# construct set of statemachine names in the system
	# also construct a map from names to objects
	smnames = set([])
	smname_to_object = {}
	for o in model.objects:
		for sm in o.type.statemachines:
			smnames.add(o.name + "'" + sm.name)
			smname_to_object[o.name + "'" + sm.name] = (o,sm)
	stateelements = set([])
	dataelements = set([])
	elements_strings = {}

	# for each state machine, order its states, and store the ids
	state_id = {}
	for c in model.classes:
		for sm in c.statemachines:
			state_nr = 0
			for s in sm.states:
				state_id[(sm,s)] = state_nr
				state_nr += 1
	# calculate state vector size
	for o in model.objects:
		# object global variables
		for v in o.type.variables:
			sizelist = gettypesize(v.type)
			for l in sizelist:
				vectorsize += l
			dataelements.add((o.name + "'" + v.name, tuple(sizelist)))
			elements_strings[o.name + "'" + v.name] = "variable " + o.name + "'" + v.name
		for sm in o.type.statemachines:
			# number of bits needed to encode states
			size = int(max(1,math.ceil(math.log(len(sm.states), 2))))
			vectorsize += size
			stateelements.add((o.name + "'" + sm.name, size))
			elements_strings[o.name + "'" + sm.name] = o.name + "'" + sm.name + " state"
			# statemachine local variables
			for v in sm.variables:
				sizelist = gettypesize(v.type)
				for l in sizelist:
					vectorsize += l
				dataelements.add((o.name + "'" + sm.name + "'" + v.name, tuple(sizelist)))
				elements_strings[o.name + "'" + sm.name + "'" + v.name] = "variable " + o.name + "'" + sm.name + "'" + v.name
	# add buffers for channels
	for ch in model.channels:
		if ch.synctype == 'async':
			typelist = []
			for t in ch.type:
				typelist += gettypesize(t)
			L = []
			for i in range(0,ch.size):
				L += typelist
			for l in L:
				vectorsize += l
			dataelements.add((ch.name, tuple(L)))
			elements_strings[ch.name] = "buffer of channel " + ch.name
	# store maximum number of bits needed to encode an automaton state
	max_statesize = 0
	for (s,i) in stateelements:
		if i > max_statesize:
			max_statesize = i
	# construct the state vector structure
	vectorstructure = []
	# construct the mapping from vector element to vector part (integer index)
	vectorelem_in_structure_map = {}
	# construct the order of states
	state_order = {}
	tmp = []
	tmpsize = 0
	intsize = 30
	if vectorsize > 30:
		intsize = 62
	vectorpart_id = 0
	state_nr = 0
	while stateelements != set([]) or dataelements != set([]):
		selected = ""
		selected_sizelist = []
		if stateelements != set([]):
			for (s,i) in stateelements:
				if i <= intsize - tmpsize:
					selected = s
					selected_sizelist = [i]
					stateelements.remove((s,i))
					state_order[state_nr] = selected
					state_nr += 1
					break
		elif dataelements != set([]):
			for (d,L) in dataelements:
				if L[0] <= intsize - tmpsize:
					selected = d
					selected_sizelist = L
					dataelements.remove((d,L))
					break
		if selected == "":
			# nothing selected; set up new int
			vectorstructure.append(tmp)
			tmp = []
			tmpsize = 0
			vectorpart_id += 1
		else:
			# add selected element to current int
			for l in selected_sizelist:
				if l <= intsize - tmpsize:
					tmp.append((selected, l))
					tmpsize += l
					vectorelem_in_structure_map[selected] = vectorpart_id
				else:
					vectorstructure.append(tmp)
					tmp = []
					tmpsize = 0
					vectorpart_id += 1
	# add final int
	if tmp != []:
		vectorstructure.append(tmp)
	vectorstructure_string = vectorstructure_to_string(elements_strings)

def get_vector_tree_navigation(p):
	"""For the given vector part (number), provide how to navigate to it from a root node"""
	global vectorstructure, smnames

	nav = []
	# are there states at this position? if so, go initially left
	t = vectorstructure[p]
	move = t[0][0] not in smnames
	nav.append(move)
	lowerbound = -1
	upperbound = -1
	for ti in range(0,len((vectorstructure))):
		if vectorstructure[ti][0][0] in smnames and not move:
			if lowerbound == -1:
				lowerbound = ti
			upperbound = ti
		elif vectorstructure[ti][0][0] not in smnames and move:
			if lowerbound == -1:
				lowerbound = ti
			upperbound = ti
	# iteratively select parts of the vector until position is left
	while lowerbound != upperbound:
		split = lowerbound + int(math.ceil((upperbound - lowerbound) / 2.0)) - 1
		if p <= split:
			upperbound = split
			nav.append(False)
		else:
			lowerbound = split+1
			nav.append(True)
	return nav

def get_bitmask(s, write):
	"""Return bitmask to extract s from statevector (flag False) or set s in statevector (flag True)"""
	global vectorstructure, vectorsize

	# first find s
	e = -1
	for t in vectorstructure:
		for (s1,i) in t:
			if s1 == s:
				e = t
				break
		if e != -1:
			break
	# compute lowerbound
	lowerbound = 2
	upperbound = 0
	for i in range(0,len(e)):
		if e[i][0] != s:
			lowerbound += e[i][1]
		else:
			upperbound = lowerbound + e[i][1]
			break
	# construct bitstring for bitmask
	bitstring = ""
	intsize = 32
	if vectorsize > 30:
		intsize = 64
	if not write:
		for i in range(0,intsize):
			if i >= lowerbound and i < upperbound:
				bitstring += "1"
			else:
				bitstring += "0"
		# convert to hex bitmask
		bitmask = hex(int(bitstring, 2))
	else:
		bitmask = "(x << " + str(intsize - upperbound) + ")"
	return str(bitmask)

def vectorstructure_to_string(D):
	"""Convert vectorstructure to string. D is dictionary to look up strings for individual elements."""
	global vectorstructure

	vs = ""
	tfirst = True
	for t in vectorstructure:
		if not tfirst:
			vs += ",\n// "
		else:
			tfirst = False
		vs += "[two bits reserved, "
		first = True
		for (s,i) in t:
			if not first:
				vs += ", "
			else:
				first = False
			vs += D[s] + ": " + str(i) + " bit(s)"
		vs += "]"
	return vs

def cudaguard(s):
	"""Returns the guard of the given statement s"""
	if s.__class__.__name__ == "Expression":
		return getinstruction(s)
	elif s.__class__.__name__ == "Composite":
		if s.guard:
			return getinstruction(s.guard)
		else:
			return ""
	return ""

def cudastatement(s,indent,o):
	"""Translates SLCO statement s to CUDA code. indent indicates how much every line needs to be indented. o is Object owning s. """

	indentspace = ""
	for i in range(0,indent):
		indentspace += " "
	output = ""
	if s.__class__.__name__ == "Assignment":
		output += getinstruction(s) + ";"
	elif s.__class__.__name__ == "Composite":
		first = True
		for e in s.assignments:
			if not first:
				output += "\n" + indentspace
			else:
				first = False
			output += getinstruction(e) + ";"
	return output

def getinstruction(s):
	"""Get the CUDA instruction for the given statement s"""
	result = ''
	if s.__class__.__name__ == "Assignment":
		result += s.left.var.name
		if s.left.index != None:
			result += "[" + getinstruction(s.left.index) + "]"
		result += " = "
		if s.left.var.type.base == 'Byte':
			result += "(elem_chartype) ("
		result += getinstruction(s.right)
		if s.left.var.type.base == 'Byte':
			result += ")"
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

def state_max_needed_vars(s):
	"""Return triple of needed variables to process each of the outgoing transitions of state s"""
	max_ints = 0
	max_bytes = 0
	max_bools = 0
	for t in outgoingtrans(s, s.parent.transitions):
		st = t.statements[0]
		L = statement_varobjects(st)
		nr_ints = 0
		nr_bytes = 0
		nr_bools = 0
		for 

def statement_write_varobjects(s):
	"""Return a list of objects to which the statement is writing"""
	W = set([])
	if s.__class__.__name__ == "Assignment":
		W.add(s.left.var)
	elif s.__class__.__name__ == "Composite":
		for i in range(0,len(s.assignments)):
			W.add(s.assignments[i].left.var)
	return list(W)

def statement_varobjects(s):
	"""Return a list of objects the statement accesses"""
	return list(set(statement_write_varobjects(s)) | statement_read_varobjects_set(s, s.parent.parent))

def statement_read_varobjects_set(s, sm):
	"""Return a set of objects from which the statement is reading. sm is the state machine owning s."""
	R = set([])
	if s.__class__.__name__ == "Assignment":
		if s.left.index != None:
			R |= statement_read_varobjects_set(s.left.index, sm)
		R |= statement_read_varobjects_set(s.right, sm)
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			R |= statement_read_varobjects_set(s.guard, sm)
		for i in range(0,len(s.assignments)):
			R |= statement_read_varobjects_set(s.assignments[i], sm)
	elif s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2" or s.__class__.__name__ == "ExprPrec1":
		R |= statement_read_varobjects_set(s.left, sm)
		if s.op != '':
			R |= statement_read_varobjects_set(s.right, sm)
	elif s.__class__.__name__ == "Primary":
		if s.ref != None:
			if s.ref.index != None:
				R |= statement_read_varobjects_set(s.ref.index, sm)
			# obtain suitable object matching name s.ref.ref
			for v1 in sm_variables(sm):
				if v1.name == s.ref.ref:
					R.add(v1)
					break
	elif s.__class__.__name__ == "VariableRef":
		if s.index != None:
			R |= statement_read_varobjects_set(s.index, sm)
		R.add(s.var)
	return R

def sm_variables(sm):
	"""Provide list of variables accessible from current state machine sm"""
	Ldict = {}
	for v in sm.parent.variables:
		Ldict[v.name] = v
	for v in sm.variables:
		Ldict[v.name] = v
	return Ldict.values()

def state_varobjects(s):
	"""Return a list of objects the state is accessing (associated to its outgoing transitions)"""
	V = set([])
	for t in outgoingtrans(s,s.parent.transitions):
		for st in t.statements:
			V |= state_varobjects_set(st, s.parent, False)
	return list(V)

def state_unguarded_varobjects(s):
	"""Return a list of objects the state is accessing. do not add objects that are guarded."""
	V = set([])
	for t in outgoingtrans(s,s.parent.transitions):
		for st in t.statements:
			V |= state_varobjects_set(st, s.parent, True)
	return list(V)

def statement_guarded_varobjects(s):
	"""Return a list of guarded objects the statement is accessing."""
	return list(set(statement_varobjects(s)) - set(state_unguarded_varobjects(s.parent.source)))

def state_varobjects_set(s, sm, guarded):
	"""Return a set of objects the state is accessing. sm is the state machine owning s. guarded indicates whether only unguarded objects should be returned."""
	R = set([])
	if s.__class__.__name__ == "Assignment":
		R.add(s.left.var)
		if s.left.index != None:
			R |= state_varobjects_set(s.left.index, sm, guarded)
		R |= state_varobjects_set(s.right, sm, guarded)
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			R |= state_varobjects_set(s.guard, sm, guarded)
		if not guarded:
			for i in range(0,len(s.assignments)):
				R |= state_varobjects_set(s.assignments[i], sm, guarded)
	elif s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2" or s.__class__.__name__ == "ExprPrec1":
		R |= state_varobjects_set(s.left, sm, guarded)
		if s.op != '':
			R |= state_varobjects_set(s.right, sm, guarded)
	elif s.__class__.__name__ == "Primary":
		if s.ref != None:
			if s.ref.index != None:
				R |= state_varobjects_set(s.ref.index, sm, guarded)
			# obtain suitable object matching name s.ref.ref
			for v1 in sm_variables(sm):
				if v1.name == s.ref.ref:
					R.add(v1)
					break
	elif s.__class__.__name__ == "VariableRef":
		if s.index != None:
			R |= state_varobjects_set(s.index, sm, guarded)
		R.add(s.var)
	return R

def get_vectorparts(L, o):
	"""For the given list of variable objects (of given Object o), return a set of vector parts that contain that info"""
	global vectorelem_in_structure_map

	P = set([])
	for v in L:
		name = scopename(v,o)
		P.add(vectorelem_in_structure_map[name])
	return P

def translate():
	"""The translation function"""
	global modelname, model, vectorstructure_string, vectorelem_in_structure_map, state_order, max_statesize, smnames, smname_to_object, state_id
	
	path, name = split(modelname)
	if name.endswith('.slco'):
		name = name[:-5]
	else:
		name = name[:-8]
	outFile = open(join(path,name + "_gpuexplore.cu"), 'w')

	# Initialize the template engine.
	jinja_env = jinja2.Environment(loader=jinja2.FileSystemLoader(join(this_folder,'../../jinja2_templates')), trim_blocks=True, lstrip_blocks=True, extensions=['jinja2.ext.loopcontrols','jinja2.ext.do',])

	# Register the filters
	jinja_env.filters['get_vector_tree_navigation'] = get_vector_tree_navigation
	jinja_env.filters['get_bitmask'] = get_bitmask
	jinja_env.filters['outgoingtrans'] = outgoingtrans
	jinja_env.filters['cudaguard'] = cudaguard
	jinja_env.filters['cudastatement'] = cudastatement
	jinja_env.filters['getlabel'] = getlabel
	jinja_env.filters['statement_varobjects'] = statement_varobjects
	jinja_env.filters['state_varobjects'] = state_varobjects
	jinja_env.filters['state_unguarded_varobjects'] = state_unguarded_varobjects
	jinja_env.filters['statement_guarded_varobjects'] = statement_guarded_varobjects
	jinja_env.filters['statement_write_varobjects'] = statement_write_varobjects
	jinja_env.filters['cudatype'] = cudatype
	jinja_env.filters['get_vectorparts'] = get_vectorparts
	jinja_env.filters['scopename'] = scopename

	# Register the tests

	# load the GPUexplore template
	template = jinja_env.get_template('gpuexplore.jinja2template')
	out = template.render(model=model, vectorsize=vectorsize, vectorstructure=vectorstructure, vectorstructure_string=vectorstructure_string, max_statesize=max_statesize, vectorelem_in_structure_map=vectorelem_in_structure_map, state_order=state_order, smnames=smnames, smname_to_object=smname_to_object, state_id=state_id)
	# write new SLCO model
	outFile.write(out)
	outFile.close()

def main(args):
	"""The main function"""
	global modelname, model, property_file, deadlock_check
	if len(args) == 0:
		print("Missing argument: SLCO model")
		sys.exit(1)
	else:
		if args[0] == '-h' or args[0] == '-help':
			print("Usage: pypy/python3 slco2gpuexplore.py [-vrsc]")
			print("")
			print("Transform an SLCO 2.0 model to CUDA source code for GPUexplore 3.0.")
			print("")
			print(" -d                    check for deadlocks")
			print(" -p                    verify given LTL property")
			sys.exit(0)
		else:
			for i in range(0,len(args)):
				if args[i] == '-d' and property_file == "":
					deadlock_check = True
				elif args[i] == '-p':
					property_file = args[i+1]
					i += 1
				else:
					modelname = args[i]

	batch = []
	if modelname.endswith('.slco'):
		batch = [modelname]
	else:
		batch = glob.glob(join(this_folder, modelname, "*.slco"))

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
		model = read_SLCO_model(file)
		print("processing model %s" % basename(file))
		try:
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

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

# state vector size (in bits)
vectorsize = 0
# set of all vector part IDs
vectorpartlist = set([])
# max state size (in bits)
max_statesize = 0
# max array size (in bits)
max_arrayindexsize = 0

# dictionary to look up signal size (in bits) for each channel
signalsize = {}
# provide number encoding for each signal, per channel
signalnr = {}

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
# maximum allocations needed to process a transition block
max_buffer_allocs = 0

# set of statemachine names in the system
smnames = set([])

# list of array names in model (with types)
arraynames = []

# dictionary providing the channels to which a given port is connected
connected_channel = {}

# LTL property
property_file = ""
# check for deadlocks?
deadlock_check = False

def RepresentsInt(s):
    try: 
        int(s)
        return True
    except ValueError:
        return False

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
	"""Return size of base of given type t, or integer if an integer is passed"""
	if isinstance(t, int):
		return t
	add = 0
	if t.base == 'Integer':
		add = 32
	elif t.base == 'Boolean':
		add = 1
	else:
		add = 8
	return add

def getlogarraysize(t):
	"""Return the log 2 of the size of array type t"""
	if t.size == 0:
		return 0
	else:
		return int(max(1,math.ceil(math.log(t.size, 2))))

def scopename(v,i,o):
	"""Return full name of variable v, possibly with index i, if constant. in case a Port is given, return name of connected Channel"""
	if v.__class__.__name__ == "Channel":
		name = v.name + str(i)
	else:
		name = o.name
		if v.parent.__class__.__name__ == "StateMachine":
			name += "'" + v.parent.name
		name += "'" + v.name
		i_str = getinstruction(i, {}, {})
		if i != None and RepresentsInt(i_str):
			name += "[" + i_str + "]"
	return name

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

# def get_bitmask(s, write):
# 	"""Return bitmask to extract s from statevector (flag False) or set s in statevector (flag True)"""
# 	global vectorstructure, vectorsize

# 	# first find s
# 	e = -1
# 	for t in vectorstructure:
# 		for (s1,i) in t:
# 			if s1 == s:
# 				e = t
# 				break
# 		if e != -1:
# 			break
# 	# compute lowerbound
# 	lowerbound = 2
# 	upperbound = 0
# 	for i in range(0,len(e)):
# 		if e[i][0] != s:
# 			lowerbound += e[i][1]
# 		else:
# 			upperbound = lowerbound + e[i][1]
# 			break
# 	# construct bitstring for bitmask
# 	bitstring = ""
# 	intsize = 32
# 	if vectorsize > 30:
# 		intsize = 64
# 	if not write:
# 		for i in range(0,intsize):
# 			if i >= lowerbound and i < upperbound:
# 				bitstring += "1"
# 			else:
# 				bitstring += "0"
# 		# convert to hex bitmask
# 		bitmask = hex(int(bitstring, 2))
# 	else:
# 		bitmask = "(x << " + str(intsize - upperbound) + ")"
# 	return str(bitmask)

def get_startbit(o):
	"""Return starting bit of object o tuple ((object, index) pair) in its corresponding part of the statevector"""
	global vectorstructure, vectorsize

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
			vs += D[s] + " " + s + ": " + str(i) + " bit(s)"
		vs += "]"
	return vs

def cudarecsizeguard(s, D):
	"""Given a ReceiveSignal statement s, return a guard referring to the size of the buffer, in case the connected channel is asynchronous"""
	global connected_channel
	c = connected_channel[s.target]
	if c.synctype == 'async':
		sizevar = D.get((c, "_size"))
		if sizevar != None:
			return sizevar[0] + "[" + str(sizevar[1]) + "] > 0"
	else:
		return ""

def cudaguard(s,D):
	"""Returns the guard of the given statement s. D is a dictionary mapping variable refs to variable names"""
	global connected_channel, signalsize, signalnr
	if s.__class__.__name__ == "Expression":
		return getinstruction(s, D, {})
	elif s.__class__.__name__ == "Composite":
		if s.guard:
			return getinstruction(s.guard, D, {})
		else:
			return ""
	elif s.__class__.__name__ == "SendSignal":
		c = connected_channel[s.target]
		print("D: " + str(D))
		sizevar = D.get((c, "_size"))
		if sizevar != None:
			return sizevar[0] + "[" + str(sizevar[1]) + "] < " + str(c.size)
	elif s.__class__.__name__ == "ReceiveSignal":
		c = connected_channel[s.target]
		if c.synctype == 'async':
			guard = ""
			if signalsize[c] > 0:
				guard += D[(c,"[0][0]")][0] + "[" + D[(c,"[0][0]")][1] + "] == " + str(signalnr[(c,s.signal)])
				if s.guard != None:
					guard += " && "
			# create a dictionary to map the params of s to buffer variables
			Drec = {}
			for i in range(0,len(s.params)):
				p = s.params[i]
				if p.index != None:
					index_str = getinstruction(p.index, {}, {})
				else:
					index_str = p.index
				Drec[(p.var.name, index_str)] = D[(c, "[" + str(i+1) + "][0]")]
			guard += getinstruction(s.guard, D, Drec)
			return guard
	return ""

def cudastatement(s,indent,o,D):
	"""Translates the unguarded part of SLCO statement s to CUDA code. indent indicates how much every line needs to be indented. o is Object owning s. D is a dictionary mapping variable refs to variable names"""
	global connected_channel

	indentspace = ""
	for i in range(0,indent):
		indentspace += "\t"
	output = ""
	if s.__class__.__name__ == "Assignment":
		output += getinstruction(s, D, {}) + ";"
	elif s.__class__.__name__ == "Composite":
		first = True
		for e in s.assignments:
			if not first:
				output += "\n" + indentspace
			else:
				first = False
			output += getinstruction(e, D, {}) + ";"
	elif s.__class__.__name__ == "SendSignal":
		c = connected_channel[s.target]
		for i in range(0,len(s.params)):
			p = s.params[i]
			if output != "":
				output += "\n" + indent
			print(D)
			output += D[(c, "[" + str(i+1) + "][0]")][0] + "[" + str(D[(c, "[" + str(i+1) + "][0]")][1]) + "] = " + getinstruction(p, D, {}) + ";"
	return output

def getinstruction(s, D, Drec):
	"""Get the CUDA instruction for the given statement s. D and Drec are dictionaries mapping variable refs to variable names. Drec is used for ReceiveSignal statements, and overrides D where applicable."""
	result = ''
	if s.__class__.__name__ == "Assignment":
		(vname,offset) = D.get(s.left.var, (s.left.var.name, None))
		result += vname
		if offset != None or s.left.index != None:
			result += "["
		if offset != None:
			result += str(offset)
			if s.left.index != None:
				result += " + "
		if s.left.index != None:
			indexresult = getinstruction(s.left.index, D, Drec)
			if (RepresentsInt(indexresult)):
				result += indexresult
			else:
				result += "idx(buffer_" + s.left.var.name + ", " + indexresult + ")"
		if offset != None or s.left.index != None:
			result += "]"
		result += " = "
		if s.left.var.type.base == 'Byte':
			result += "(elem_chartype) ("
		result += getinstruction(s.right, D, Drec)
		if s.left.var.type.base == 'Byte':
			result += ")"
	elif s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2" or s.__class__.__name__ == "ExprPrec1":
		if s.op != '':
			result += getinstruction(s.left, D, Drec) + " " + operator(s.op) + " " + getinstruction(s.right, D, Drec)
		else:
			result += getinstruction(s.left, D, Drec)
	elif s.__class__.__name__ == "Primary":
		result += sign(s.sign)
		if s.sign == "not":
			result += "("
		if s.value != None:
			newvalue = s.value
			result += str(newvalue).lower()
		elif s.ref != None:
			vname = s.ref.ref
			offset = None
			# look for an exact (name, index) match in Drec
			if s.ref.index != None:
				index_str = getinstruction(s.ref.index, {}, {})
			else:
				index_str = s.ref.index
			(vname,offset) = Drec.get((s.ref.ref, index_str), (s.ref.ref, None))
			if vname == s.ref.ref:
				# look for a match on s.ref.ref in D
				for r in D.keys():
					print("here")
					print(s.ref.ref)
					if not isinstance(r, tuple):
						print(s.ref.ref + " " + r.name)
						if s.ref.ref == r.name:
							vname = D[r][0]
							offset = D[r][1]
							break
			result += vname
			if offset != None or s.ref.index != None:
				result += "["
			if offset != None:
				result += str(offset)
				if s.ref.index != None:
					result += " + "
			if s.ref.index != None:
				indexresult = getinstruction(s.ref.index, D, Drec)
				if (RepresentsInt(indexresult)):
					result += indexresult
				else:
					result += "idx(buffer_" + s.ref.ref + ", " + indexresult + ")"
			if offset != None or s.ref.index != None:
				result += "]"
		else:
			result += '(' + getinstruction(s.body, D, Drec) + ')'
		if s.sign == "not":
			result += ")"
	elif s.__class__.__name__ == "VariableRef":
		(vname,offset) = D.get(s.var, (s.var.name, None))
		result += vname
		if offset != None or s.index != None:
			result += "["
		if offset != None:
			result += str(offset)
			if s.index != None:
				result += " + "
		if s.index != None:
			indexresult = getinstruction(s.index, D, Drec)
			if (RepresentsInt(indexresult)):
				result += indexresult
			else:
				result += "idx(buffer_" + s.var.name + ", " + indexresult + ")"
		if offset != None or s.index != None:
			result += "]"
	return result

def transition_read_varrefs(t, only_unguarded):
	"""Return a set of variable refs appearing in block of transition t"""
	R = set([])
	sm = t.parent
	for st in t.statements:
		R |= statement_read_varrefs(st, sm, only_unguarded)
	filtered_R = set([])
	Vseen = set([])
	for (v,i) in R:
		i_str = getinstruction(i, {}, {})
		if (v,i_str) not in Vseen:
			Vseen.add((v,i_str))
			filtered_R.add((v,i))
	return filtered_R

def transition_sorted_dynamic_read_varrefs(t, only_unguarded):
	"""Return a sorted list of variable refs involving dynamic indexing, in block of transition t. They are sorted on dependency."""
	R = set([])
	sm = t.parent
	for st in t.statements:
		Rtmp = statement_read_varrefs(st, sm, True)
		if not only_unguarded:
			Rtmp_all = statement_read_varrefs(st, sm, False)
			Rtmp = Rtmp_all - Rtmp
		R |= Rtmp
	# only keep refs with dynamic indexing
	R2 = set([])
	for (v,i) in R:
		if v.__class__.__name__ != "Channel":
			i_str = getinstruction(i, {}, {})
			if i != None and not RepresentsInt(i_str):
				R2.add((v,i))
	L = []
	R = set([])
	while R2 != set([]):
		for (v,i) in R2:
			R3 = statement_read_varrefs(i, sm, only_unguarded)
			add = True
			for (v2,i2) in R3:
				if (v2,i2) in R2:
					add = False
					break
			if add:
				L.append((v,i))
			else:
				R.add((v,i))
		R2 = R
		R = set([])
	return L

def statement_varrefs(s, sm):
	"""Return a set of variable refs appearing in statement s. sm is the state machine owning s."""
	global connected_channel, signalsize
	R = set([])
	if s.__class__.__name__ == "Assignment":
		R.add((s.left.var, s.left.index))
		if s.left.index != None:
			R |= statement_varrefs(s.left.index, sm)
		R |= statement_varrefs(s.right, sm)
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			R |= statement_varrefs(s.guard, sm)
		for i in range(0,len(s.assignments)):
			R |= statement_varrefs(s.assignments[i], sm)
	elif s.__class__.__name__ == "SendSignal":
		c = connected_channel[s.target]
		if c.synctype == 'async':
			# add channel with index '_size' to represent 'size' variable
			R.add((c, "_size"))
			# add channel with integer indices to represent items of a Message
			if signalsize[c] > 0:
				R.add((c, "[0][0]"))
			for i in range(1,len(c.type)+1):
				R.add((c, "[" + str(i) + "][0]"))
			for p in s.params:
				R |= statement_varrefs(p, sm)
	elif s.__class__.__name__ == "ReceiveSignal":
		c = connected_channel[s.target]
		if c.synctype == 'async':
			# add channel with index "_size" to represent 'size' variable
			R.add((c, "_size"))
			# add channel with integer indices to represent items of a Message
			if signalsize[c] > 0:
				R.add((c, "[0][0]"))
			for i in range(1,len(c.type)+1):
				R.add((c, "[" + str(i) + "][0]"))
			Messagerefs = set([])
			for p in s.params:
				Messagerefs.add((p.var.name, getinstruction(p.index, {}, {})))
				if p.index != None:
					R |= statement_varrefs(p.index, sm)
			Rguard = statement_varrefs(s.guard, sm)
			for (v,j) in Rguard:
				if (v.name, getinstruction(j, {}, {})) not in Messagerefs:
					R.add((v,j))
		# else:
		# 	for p in s.params:
		# 		R |= statement_varrefs(p, sm)
		# 	R |= statement_varrefs(s.guard, sm)
	elif s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2" or s.__class__.__name__ == "ExprPrec1":
		R |= statement_varrefs(s.left, sm)
		if s.op != '':
			R |= statement_varrefs(s.right, sm)
	elif s.__class__.__name__ == "Primary":
		if s.ref != None:
			if s.ref.index != None:
				R |= statement_varrefs(s.ref.index, sm)
			# obtain suitable object matching name s.ref.ref
			for v1 in sm_variables(sm):
				if v1.name == s.ref.ref:
					R.add((v1, s.ref.index))
					break
		if s.body != None:
			R |= statement_varrefs(s.body, sm)
	elif s.__class__.__name__ == "VariableRef":
		if s.index != None:
			R |= statement_varrefs(s.index, sm)
		R.add((s.var, s.index))
	return R

def statement_write_varrefs(s):
	"""Return a list of variable refs to which the statement is writing"""
	W = set([])
	if s.__class__.__name__ == "Assignment":
		W.add((s.left.var, s.left.index))
	elif s.__class__.__name__ == "Composite":
		for i in range(0,len(s.assignments)):
			W.add((s.assignments[i].left.var, s.assignments[i].left.index))
	return W

def statement_read_varrefs(s, sm, only_unguarded):
	"""Return a set of variable refs from which the statement is reading. sm is the state machine owning s. only_unguarded indicates whether only the unguarded objects (true) or all objects (false) should be returned."""
	global connected_channel, signalsize
	R = set([])
	if s.__class__.__name__ == "Assignment":
		if s.left.index != None:
			R |= statement_read_varrefs(s.left.index, sm, only_unguarded)
		R |= statement_read_varrefs(s.right, sm, only_unguarded)
	elif s.__class__.__name__ == "Composite":
		if s.guard != None:
			R |= statement_read_varrefs(s.guard, sm, only_unguarded)
		if s.guard == None or not only_unguarded:
			for i in range(0,len(s.assignments)):
				R |= statement_read_varrefs(s.assignments[i], sm, only_unguarded)
	elif s.__class__.__name__ == "SendSignal":
		c = connected_channel[s.target]
		if c.synctype == 'async':
			# add channel with index "_size" to represent 'size' variable
			R.add((c, "_size"))
			# below: also holds for sync
			if not only_unguarded:
				for p in s.params:
					R |= statement_read_varrefs(p, sm, only_unguarded)			
	elif s.__class__.__name__ == "ReceiveSignal":
		c = connected_channel[s.target]
		if c.synctype == 'async':
			# Note: checking size of buffer is NOT part of unguarded behaviour! (instead, this is checked in an earlier stage)
			# add channel with indices to represent the various items in a Message
			if signalsize[c] > 0:
				R.add((c, "[0][0]"))
			for i in range(1,len(c.type)+1):
				R.add((c, "[" + str(i) + "][0]"))
			# below: also holds for sync
			Messagerefs = set([])
			for p in s.params:
				Messagerefs.add((p.var.name, getinstruction(p.index, {}, {})))
				if p.index != None:
					R |= statement_read_varrefs(p.index, sm, only_unguarded)
			R1 = statement_read_varrefs(s.guard, sm, only_unguarded)
			for (v,j) in R1:
				if (v.name, getinstruction(j, {}, {})) not in Messagerefs:
					R.add((v,j))
	elif s.__class__.__name__ == "Expression" or s.__class__.__name__ == "ExprPrec4" or s.__class__.__name__ == "ExprPrec3" or s.__class__.__name__ == "ExprPrec2" or s.__class__.__name__ == "ExprPrec1":
		R |= statement_read_varrefs(s.left, sm, only_unguarded)
		if s.op != '':
			R |= statement_read_varrefs(s.right, sm, only_unguarded)
	elif s.__class__.__name__ == "Primary":
		if s.ref != None:
			if s.ref.index != None:
				R |= statement_read_varrefs(s.ref.index, sm, only_unguarded)
			# obtain suitable object matching name s.ref.ref
			for v1 in sm_variables(sm):
				if v1.name == s.ref.ref:
					R.add((v1, s.ref.index))
					break
		if s.body != None:
			R |= statement_read_varrefs(s.body, sm, only_unguarded)
	elif s.__class__.__name__ == "VariableRef":
		if s.index != None:
			R |= statement_read_varrefs(s.index, sm, only_unguarded)
		R.add((s.var, s.index))
	return R

def get_vars(L):
	"""Given a list of variable refs, return the corresponding set of vars"""
	S = set([])
	for (v,j) in L:
		S.add(v)
	return S

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
			V |= statement_varobjects_set(st, s.parent, False)
	return list(V)

def state_unguarded_varobjects(s):
	"""Return a list of objects the state is accessing. do not add objects that are guarded."""
	V = set([])
	for t in outgoingtrans(s,s.parent.transitions):
		for st in t.statements:
			V |= statement_varobjects_set(st, s.parent, True)
	return list(V)

def statement_guarded_varobjects(s):
	"""Return a list of guarded objects the statement is accessing."""
	return list(set(statement_varobjects(s)) - set(state_unguarded_varobjects(s.parent.source)))

def get_buffer_allocs(s):
	"""Return info on number of variable allocations to do for evaluation of transition blocks of outgoing transitions of state s"""
	global vectorelem_in_structure_map, signalsize
	sm = s.parent
	max_32 = 0
	max_16 = 0
	max_8 = 0
	max_bool = 0
	for t in outgoingtrans(s, sm.transitions):
		Vseen = set([])
		O = set([])
		for st in t.statements:
			# O is set of variable refs occurring in block of t
			O |= statement_varrefs(st, sm)
		nr_32 = 0
		nr_8 = 0
		nr_bool = 0
		print(O)
		for (v,i) in O:
			if v.__class__.__name__ != "Channel":
				i_str = getinstruction(i, {}, {})
			else:
				i_str = i
			if (v,i_str) not in Vseen:
				Vseen.add((v,i_str))
				if v.__class__.__name__ == "Channel":
					# access channel buffer item or its size
					size = vectorelem_in_structure_map[v.name + i][0]
					print(i)
					print(size)
					if size <= 1:
						nr_bool += 1
					elif size <= 8:
						nr_8 += 1
					else:
						nr_32 += 1
				elif v.type.base == 'Integer':
					nr_32 += 1
				elif v.type.base == 'Byte':
					nr_8 += 1
				else:
					nr_bool += 1
		# record maxima
		if nr_32 > max_32:
			max_32 = nr_32
		if nr_8 > max_8:
			max_8 = nr_8
		if nr_bool > max_bool:
			max_bool = nr_bool
		# add additional 16-bit integers (if needed) for pointers to store new vector trees
		Vseen = set([])
		O = set([])
		for st in t.statements:
			O |= statement_write_varrefs(st)
		for (v,i) in O:
			i_str = getinstruction(i, {}, {})
			Vseen.add((v,i_str))
		if len(Vseen) > 2*max_32 + max_16:
			max_16 += (2*max_32 + max_16) - len(Vseen)
	return (max_32, max_16, max_8, max_bool)

def get_buffer_arrayindex_allocs(s):
	"""Return info on variable allocations needed to do bookkeeping on dynamically accessing SLCO array elements, for outgoing transitions of state s"""
	sm = s.parent
	allocs = {}
	for t in outgoingtrans(s, sm.transitions):
		Vseen = set([])
		access_counters = {}
		dynamic_access_seen = set([])
		O = set([])
		for st in t.statements:
			O |= statement_varrefs(st, sm)
		for (v,i) in O:
			# is v an array?
			if v.__class__.__name__ != "Channel": 
				if v.type.size > 0:
					i_str = getinstruction(i, {}, {})
					if (v,i_str) not in Vseen:
						Vseen.add((v,i_str))
						count = access_counters.get(v, 0)
						count += 1
						access_counters[v] = count
						if not RepresentsInt(i_str):
							dynamic_access_seen.add(v)
		for v in dynamic_access_seen:
			count1 = allocs.get(v, 0)
			count2 = access_counters.get(v, 0)
			if count2 > count1:
				allocs[v] = count2
	return allocs

def map_variables_on_buffer(t):
	"""Construct for block of given transition t a mapping from variables to buffer variables"""
	global vectorelem_in_structure_map, connected_channel
	sm = t.parent
	# counters
	current_32 = 0
	current_8 = 0
	current_bool = 0
	O = set([])
	for st in t.statements:
		O |= statement_varrefs(st, sm)
	M = {}
	access_counters = {}
	Vseen = set([])
	for (v,i) in O:
		if not is_async_channel(v):
			i_str = getinstruction(i, {}, {})
			if (v,i_str) not in Vseen:
				Vseen.add((v,i_str))
				count = access_counters.get(v, 0)
				count += 1
				access_counters[v] = count
		else:
			access_counters[v] = 1
	for v in access_counters.keys():
		if v.__class__.__name__ == "Channel":
			size = vectorelem_in_structure_map[v.name + "_size"][0]
			if size <= 1:
				M[(v, "_size")] = ("buf1", current_bool)
				current_bool += 1
			elif size <= 8:
				M[(v, "_size")] = ("buf8", current_8)
				current_8 += 1
			else:
				M[(v, "_size")] = ("buf32", current_32)
				current_32 += 1
			for i in range(0,len(v.type)+1):
				if i == 0:
					size = signalsize[v]
				else:
					size = gettypesize(v.type[i-1])
				vindex = "[" + str(i) + "][0]"
				if size > 0:
					if size == 1:
						M[(v, vindex)] = ("buf1", current_bool)
						current_bool += 1
					elif size <= 8:
						M[(v, vindex)] = ("buf8", current_8)
						current_8 += 1
					else:
						M[(v, vindex)] = ("buf32", current_32)
						current_32 += 1
		elif gettypesize(v.type) == 32:
			M[v] = ("buf32", current_32)
			current_32 += access_counters[v]
		elif gettypesize(v.type) == 8:
			M[v] = ("buf8", current_8)
			current_8 += access_counters[v]
		else:
			M[v] = ("buf1", current_bool)
			current_bool += access_counters[v]
	return M

def get_vectorparts(L, o):
	"""For the given set of variable refs (of given Object o), return a sorted list of vector parts that contain that info"""
	global vectorelem_in_structure_map, connected_channel

	P = set([])
	for (v,i) in L:
		if v.__class__.__name__ != "Channel":
			i_str = getinstruction(i, {}, {})
		else:
			i_str = i
		name = scopename(v,i,o)
		PIDs = vectorelem_in_structure_map[name]
		P.add(PIDs[1][0])
		if len(PIDs) > 2:
			P.add(PIDs[2][0])
	return sorted(list(P))

def get_remaining_vectorparts(L, o, VPs):
	"""Return a sorted list of vector parts that are needed to obtain values of given variable refs in L, that are not covered by list of vector parts VPs"""
	global vectorelem_in_structure_map

	VPset = set(VPs)
	P = set([])
	for (v,i) in L:
		if v.__class__.__name__ != "Channel":
			i_str = getinstruction(i, {}, {})
			name = scopename(v,None,o)
			if RepresentsInt(i_str):
				name += "[" + i_str + "]"
			PIDs = vectorelem_in_structure_map[name]
			S = set([PIDs[1][0]])
			if len(PIDs) > 2:
				S.add(PIDs[2][0])
			if not S.issubset(VPset):
				P |= S
	return sorted(list(P))

def vectorparts_not_covered((v, i), o, VPs):
	"""Return whether or not the vectorparts needed for variable ref (v,i) are in list of vector parts VPs"""
	global vectorelem_in_structure_map

	if v.__class__.__name__ == "Channel":
		return False
	VPset = set(VPs)
	i_str = getinstruction(i, {}, {})
	name = scopename(v,None,o)
	if RepresentsInt(i_str):
		name += "[" + i_str + "]"
	PIDs = vectorelem_in_structure_map[name]
	S = set([PIDs[1][0]])
	if len(PIDs) > 2:
		S.add(PIDs[2][0])
	return not S.issubset(VPset)

# filter to produce difference between two lists
def difference(L1, L2):
	L = []
	L2set = set(L2)
	for l in L1:
		if l not in L2set:
			L.append(l)
	return L

def is_async_channel(name):
	"""Return whether given name refers to an asynchronous channel in model"""
	global model

	for c in model.channels:
		if name == c.name:
			if c.synctype == 'async':
				return True
			else:
				return False
	return False

def is_state(name):
	"""Returns whether given name refers to a state in model"""
	global model

	for o in model.objects:
		c = o.type
		for sm in c.statemachines:
			if name == o.name + "'" + sm.name:
				return True
	return False

# Test to check if given channel is asynchronous
def is_async(c):
	return c.synctype == 'async'

# Test to check if given variable ref has dynamic indexing
def no_dynamic_indexing(v):
	if v[0].__class__.__name__ == "Channel":
		return True
	if v[1] == None:
		return True
	i_str = getinstruction(v[1], {}, {})
	return RepresentsInt(i_str)

def has_dynamic_indexing(v, t):
	"""Returns whether for array v, dynamic indexing is done in the block of transition t"""
	if v.__class__.__name__ != "Channel":
		sm = t.parent
		O = set([])
		for st in t.statements:
			O |= statement_varrefs(st, sm)
		for (v1,i) in O:
			if v1 == v:
				if i != None:
					i_str = getinstruction(i, {}, {})
					if not RepresentsInt(i_str):
						return True
	return False

# Filter for debugging
def debug(text):
	print(text)
	return ''

def preprocess():
	"""Preprocessing of model"""
	global model, vectorsize, vectorstructure, vectorstructure_string, smnames, vectorelem_in_structure_map, max_statesize, state_order, smname_to_object, state_id, arraynames, max_arrayindexsize, max_buffer_allocs, vectorpartlist, connected_channel, signalsize, signalnr

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

	# construct dictionary providing connected channel of given port
	connected_channel = {}
	for c in model.channels:
		connected_channel[c.port0] = c
		connected_channel[c.port1] = c

	# determine number of bits needed to represent channel signals for each channel, and encode for each channel the possible signals
	signalsize = {}
	signalnr = {}
	signals = {}
	for c in model.classes:
		for sm in c.statemachines:
			for t in sm.transitions:
				for st in t.statements:
					if st.__class__.__name__ == "ReceiveSignal" or st.__class__.__name__ == "SendSignal":
						c = connected_channel[st.target]
						S = signals.get(c, set([]))
						S.add(st.signal)
						signals[c] = S
	# determine number of bits needed
	for c, S in signals.items():
		bitcount = int(math.ceil(math.log(len(S), 2)))
		signalsize[c] = bitcount
		# encode signals
		nr = 0
		for s in S:
			signalnr[(c,s)] = nr
			nr += 1

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
			size = gettypesize(v.type)
			dimension = 0
			if v.type.size > 1:
				dimension = v.type.size
			vectorsize += (size*dimension)
			dataelements.add((o.name + "'" + v.name, tuple([size]), dimension))
		for sm in o.type.statemachines:
			# number of bits needed to encode states
			size = int(max(1,math.ceil(math.log(len(sm.states), 2))))
			vectorsize += size
			stateelements.add((o.name + "'" + sm.name, size))
			# statemachine local variables
			for v in sm.variables:
				size = gettypesize(v.type)
				dimension = 0
				if v.type.size > 1:
					dimension = v.type.size
				vectorsize += (size*dimension)
				dataelements.add((o.name + "'" + sm.name + "'" + v.name, tuple([size]), dimension))
	# add buffers for channels
	for ch in model.channels:
		if ch.synctype == 'async':
			typelist = [signalsize[ch]]
			for t in ch.type:
				typelist.append(gettypesize(t))
			dimension = 1
			if ch.size > 1:
				dimension = ch.size
			dataelements.add((ch.name, tuple(typelist), dimension))
	# store maximum number of bits needed to encode an automaton state
	max_statesize = 0
	for (s,i) in stateelements:
		if i > max_statesize:
			max_statesize = i
	# store maximum number of bits needed for indices of arrays and channel buffers
	max_arrayindexsize = 0
	maxsize = 0
	for c in model.classes:
		for v in c.variables:
			if v.type.size > maxsize:
				maxsize = v.type.size
		for sm in c.statemachines:
			for v in sm.variables:
				if v.type.size > maxsize:
					maxsize = v.type.size
	for c in model.channels:
		if c.size > maxsize:
			maxsize = c.size
	max_arrayindexsize = int(max(1,math.ceil(math.log(maxsize, 2))))
	# construct the state vector structure
	vectorstructure = []
	# construct the mapping from vector element to vector part (integer index)
	vectorelem_in_structure_map = {}
	# construct the order of states and variables in the vectors
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
		selected_dim = 0
		selected_sizelist = []
		if stateelements != set([]):
			for (s,i) in stateelements:
				if i <= intsize - tmpsize:
					selected = s
					selected_sizelist = [i]
					stateelements.remove((s,i))
					state_order[state_nr] = selected
					state_nr += 1
					elements_strings[selected] = "state"
					break
		elif dataelements != set([]):
			for (d,slist,dimension) in dataelements:
				if slist[0] <= intsize - tmpsize:
					selected = d
					selected_sizelist = slist
					selected_dim = dimension
					dataelements.remove((d,slist,dimension))
					break
		if selected == "":
			# nothing selected; add an element partially to current part
			if stateelements != set([]):
				for (s,i) in stateelements:
					selected = s
					selected_sizelist = [i]
					stateelements.remove((s,i))
					state_order[state_nr] = selected
					state_nr += 1
					elements_strings[selected] = "state"
					break					
			elif dataelements != set([]):
				for (d,slist,dimension) in dataelements:
					selected = d
					selected_sizelist = slist
					selected_dim = dimension
					dataelements.remove((d,slist,dimension))
					break
		if selected != "":
			# if we are adding a channel buffer, add counters if needed
			if is_async_channel(selected):
				sname = selected
				# create a new part if the current one is full
				if intsize - tmpsize == 0:
					vectorstructure.append(tmp)
					tmp = []
					tmpsize = 0
					vectorpart_id += 1
				dimbits = int(max(1,math.ceil(math.log(selected_dim, 2))))
				added_size = min(dimbits, intsize - tmpsize)
				tmp.append((sname + "_size", added_size))
				PIDs = [dimbits, (vectorpart_id, (intsize)-(tmpsize+added_size), added_size)]
				tmpsize += added_size
				if dimbits - added_size > 0:
					# add remainder of element to new vector part
					vectorstructure.append(tmp)
					tmp = [(sname + "_size", dimbits - added_size)]
					tmpsize = dimbits - added_size
					vectorpart_id += 1
					PIDs.append((vectorpart_id, intsize-(dimbits - added_size), dimbits - added_size))
				vectorelem_in_structure_map[sname + "_size"] = PIDs
				elements_strings[sname + "_size"] = "channel size counter"
			# add selected element to current (and possibly subsequent) vector part(s)
			for i in range(0,max(1,selected_dim)):
				for j in range(0,len(selected_sizelist)):
					sname = selected
					sindex = ""
					if is_async_channel(selected):
						sindex = "[" + str(j) + "][" + str(i) + "]"
					elif selected_dim > 0:
						sindex = "[" + str(i) + "]"
					l = selected_sizelist[j]
					if l > 0:
						# create a new part if the current one is full
						if intsize - tmpsize == 0:
							vectorstructure.append(tmp)
							tmp = []
							tmpsize = 0
							vectorpart_id += 1
						added_size = min(l, intsize - tmpsize)
						tmp.append((sname + sindex, added_size))
						PIDs = [l, (vectorpart_id, (intsize)-(tmpsize+added_size), added_size)]
						tmpsize += added_size
						if l - added_size > 0:
							# add remainder of element to new vector part
							vectorstructure.append(tmp)
							tmp = [(sname + sindex, l - added_size)]
							tmpsize = l - added_size
							vectorpart_id += 1
							PIDs.append((vectorpart_id, intsize-(l - added_size), l - added_size))
						vectorelem_in_structure_map[sname + sindex] = PIDs
						if elements_strings.get(sname + sindex) == None:
							if is_async_channel(sname):
								elements_strings[sname + sindex] = "channel buffer part"
							else:
								elements_strings[sname + sindex] = "variable"
	# add final vector part
	if tmp != []:
		vectorstructure.append(tmp)
	vectorstructure_string = vectorstructure_to_string(elements_strings)
	# create list of array names and channel buffer names
	arraynames = []
	for o in model.objects:
		for v in o.type.variables:
			if v.type.size > 0:
				arraynames.append((o.name + "'" + v.name, v.type, v.type.size))
		for sm in o.type.statemachines:
			for v in sm.variables:
				if v.type.size > 0:
					arraynames.append((o.name + "'" + sm.name + "'" + v.name, v.type, v.type.size))
	for c in model.channels:
		if c.synctype == 'async':
			if signalsize[c] > 0:
				arraynames.append((c.name + "[0]", signalsize[c], c.size))
			for i in range(0,len(c.type)):
				arraynames.append((c.name + "[" + str(i+1) + "]", c.type[i], c.size))
	# compute maximum number of buffer variable allocs needed for transition block processing
	max_buffer_allocs = [0,0,0]
	for c in model.classes:
		for sm in c.statemachines:
			for s in sm.states:
				allocs = get_buffer_allocs(s)
				if allocs[0] > max_buffer_allocs[0]:
					max_buffer_allocs[0] = allocs[0]
				if allocs[2] > max_buffer_allocs[1]:
					max_buffer_allocs[1] = allocs[2]
				if allocs[3] > max_buffer_allocs[2]:
					max_buffer_allocs[2] = allocs[3]
	max_buffer_allocs = max(max_buffer_allocs)
	# define set of vector parts
	vectorpartlist = [i for i in range(0,len(vectorstructure))]
	print(vectorelem_in_structure_map)

def translate():
	"""The translation function"""
	global modelname, model, vectorstructure_string, vectorelem_in_structure_map, state_order, max_statesize, smnames, smname_to_object, state_id, arraynames, max_arrayindexsize, max_buffer_allocs, vectorpartlist, signalsize, connected_channel
	
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
	jinja_env.filters['outgoingtrans'] = outgoingtrans
	jinja_env.filters['cudarecsizeguard'] = cudarecsizeguard
	jinja_env.filters['cudaguard'] = cudaguard
	jinja_env.filters['cudastatement'] = cudastatement
	jinja_env.filters['getinstruction'] = getinstruction
	jinja_env.filters['getlabel'] = getlabel
	jinja_env.filters['transition_read_varrefs'] = transition_read_varrefs
	jinja_env.filters['transition_sorted_dynamic_read_varrefs'] = transition_sorted_dynamic_read_varrefs
	jinja_env.filters['statement_varrefs'] = statement_varrefs
	jinja_env.filters['statement_write_varrefs'] = statement_write_varrefs
	jinja_env.filters['state_unguarded_varobjects'] = state_unguarded_varobjects
	jinja_env.filters['statement_guarded_varobjects'] = statement_guarded_varobjects
	jinja_env.filters['cudatype'] = cudatype
	jinja_env.filters['get_vectorparts'] = get_vectorparts
	jinja_env.filters['get_remaining_vectorparts'] = get_remaining_vectorparts
	jinja_env.filters['scopename'] = scopename
	jinja_env.filters['gettypesize'] = gettypesize
	jinja_env.filters['getlogarraysize'] = getlogarraysize
	jinja_env.filters['get_buffer_allocs'] = get_buffer_allocs
	jinja_env.filters['get_buffer_arrayindex_allocs'] = get_buffer_arrayindex_allocs
	jinja_env.filters['map_variables_on_buffer'] = map_variables_on_buffer
	jinja_env.filters['is_state'] = is_state
	jinja_env.filters['has_dynamic_indexing'] = has_dynamic_indexing
	jinja_env.filters['difference'] = difference
	jinja_env.filters['get_vars'] = get_vars
	jinja_env.filters['debug'] = debug

	# Register the tests
	jinja_env.tests['is_async'] = is_async
	jinja_env.tests['no_dynamic_indexing'] = no_dynamic_indexing
	jinja_env.tests['vectorparts_not_covered'] = vectorparts_not_covered

	# load the GPUexplore template
	template = jinja_env.get_template('gpuexplore.jinja2template')
	out = template.render(model=model, vectorsize=vectorsize, vectorstructure=vectorstructure, vectorstructure_string=vectorstructure_string, max_statesize=max_statesize, vectorelem_in_structure_map=vectorelem_in_structure_map, state_order=state_order, smnames=smnames, smname_to_object=smname_to_object, state_id=state_id, arraynames=arraynames, max_arrayindexsize=max_arrayindexsize, max_buffer_allocs=max_buffer_allocs, vectorpartlist=vectorpartlist, connected_channel=connected_channel)
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

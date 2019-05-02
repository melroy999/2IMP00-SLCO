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
# structure of vector
vectorstructure = []
vectorstructure_string = ""

# set of statemachine names in the system
smnames = set([])

# LTL property
property_file = ""
# check for deadlocks?
deadlock_check = False

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
		for i in range(0,t.size):
			L.append(add)
	else:
		L.append(add)
	return L

def preprocess():
	"""Preprocessing of model"""
	global model, vectorsize, vectorstructure, vectorstructure_string, smnames

	# construct set of statemachine names in the system
	smnames = set([])
	for o in model.objects:
		for sm in o.type.statemachines:
			smnames.add(o.name + "'" + sm.name)
	stateelements = set([])
	dataelements = set([])
	elements_strings = {}
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
	# construct the state vector structure
	vectorstructure = []
	tmp = []
	tmpsize = 0
	intsize = 30
	if vectorsize > 30:
		intsize = 62
	while stateelements != set([]) or dataelements != set([]):
		selected = ""
		selected_sizelist = []
		if stateelements != set([]):
			for (s,i) in stateelements:
				if i <= intsize - tmpsize:
					selected = s
					selected_sizelist = [i]
					stateelements.remove((s,i))
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
		else:
			# add selected element to current int
			for l in selected_sizelist:
				if l <= intsize - tmpsize:
					tmp.append((selected, l))
					tmpsize += l
				else:
					vectorstructure.append(tmp)
					tmp = []
					tmpsize = 0
	vectorstructure_string = vectorstructure_to_string(elements_strings)

def get_vector_tree_navigation(s):
	"""For the given element s (string), provide how to navigate to the right vector int from a root node"""
	global vectorstructure, smnames

	nav = []
	# lookup element s
	position = -1
	for ti in range(0,len(vectorstructure)):
		for (s1,i) in vectorstructure[ti]:
			if s == s1:
				position = ti
				break
		if position != -1:
			break
	# are there states at this position? if so, go initially left
	t = vectorstructure[position]
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
	print(smnames)
	print(vectorstructure)
	print(lowerbound)
	print(upperbound)
	# iteratively select paets of the vector until position is left
	while lowerbound != upperbound:
		split = lowerbound + int(math.ceil((upperbound - lowerbound) / 2.0)) - 1
		if position <= split:
			upperbound = split
			nav.append(False)
		else:
			lowerbound = split+1
			nav.append(True)
	return nav

def get_bitmask(s):
	"""Return bitmask to extract s from statevector"""
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
	print(e)
	for i in range(0,len(e)):
		if e[i][0] != s:
			lowerbound += e[i][1]
		else:
			upperbound = lowerbound + e[i][1]
			break
	# construct bitstring for bitmask
	print("check")
	print(lowerbound)
	print(upperbound)
	bitstring = ""
	intsize = 32
	if vectorsize > 30:
		intsize = 64
	for i in range(0,intsize):
		if i >= lowerbound and i < upperbound:
			bitstring += "1"
		else:
			bitstring += "0"
	print(bitstring)
	# convert to hex bitmask
	bitmask = hex(int(bitstring, 2))
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

def translate():
	"""The translation function"""
	global modelname, model, vectorstructure_string
	
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

	# Register the tests

	# load the GPUexplore template
	template = jinja_env.get_template('gpuexplore.jinja2template')
	out = template.render(model=model, vectorsize=vectorsize, vectorstructure=vectorstructure, vectorstructure_string=vectorstructure_string)
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

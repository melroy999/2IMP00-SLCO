# The REFINER tool, v.0.92 by Anton Wijs, 2013

# Added with v.0.92:
# - fixed synchronisation condition: required link between patterns of a rule is now checked
# - support for new rulesystem file format; all info now in one format
# - rulesystem description now contains abstract sync rules, before and after transformation;
#   these are mapped to concrete sync rules of input network

# Added with v.0.91:
# - interfaces to isolate parts of a system / rule vector for analysis purposes
# - new weakened application conditions (removal completeness, new synchronisation condition)
# - exclusive glue-states

# for timing measurements
from __future__ import with_statement
import time
import sys, string, collections, itertools, copy, pickle
import os
import subprocess
#from shutil import copyfile
from graphfunctions import generateLTS
from collections import deque, Counter
import re
import multiprocessing
import config
import glob
from rule import *
from shutil import copyfile
#from test.test_dis import outer

import network
import aut
import sync_law
import action

# import configurations
import plugin_loader
import config
import config_options as opt

# plugins
loaded_plugins = []
# constant label to indicate accepting state
ACCEPT = 'accept'
# constant labels for ICC
ICC_CURRENTPROC_PREFIX = 'iccproc-'
ICC_PREVPROC_PREFIX = 'iccprevproc-'
ICC_BOTHPROC_PREFIX = 'iccbothproc-'
ICC_NOTPREVPROC_PREFIX = 'not-iccprevproc-'

#the processes
proccounter = 0
procfiles = []
# the process headers
procsheaders = []
# the standard process LTSs, structurally ordered by source states
procs = []
# the number of process LTSs, before transformation
procs_orig_size = 0
# the reversed process LTSs, structurally ordered by target states
revprocs = []
# the action process LTSs, structurally ordered by action (transition) labels
actprocs = []
# the process LTSs after a transformation
transformed_procs = []
new_procfiles = []
# the process headers after a transformation
transformed_procsheaders = []
# a mapping from new rule states (right hand patterns) to states in procs
transformed_procs_new_states = []
# set of action patterns to be hidden (-a option)
hideactions = []
# set of concrete actions hidden
hiddenactions = set([])


#data for state space searches
systemLTSheader = []
systemLTSheader.append('0')
systemLTSheader.append('0')
systemLTSheader.append('0')
systemtrans = {}
systemactset = set([])
hashtable = {}
revhashtable = {}
systemstatecounter = 0
systemtranscounter = 0

# set of tau-diverging states
divergencyset = set([])
# sets of non-diverging process states
procndivsets = []

# a rule system is a finite set of LTS-pairs
RS = []
# add rules of rule system
RS_add = []
# tuples of sets of prefixes of actions in left and right patterns, respectively
RS_actprefixsets = []
# description (i.e. list of rule id's) how to construct vectors of (dependent) transformation rules
RS_vector = []
# number of rule instances in RS_vector that are transform rules (as opposed to add rules)
RS_vector_nr_transrules = 0
# functions assigning rule id (owner) to actions; two functions in list, first for left patterns, second for right
RS_ownsaction = [{},{}]
# syncrules in the rulesystem w.r.t. the left-hand patterns
RS_left_syncrules = {}
RS_left_syncactions = []
# syncrules in the rulesystem w.r.t. the left-hand patterns, optimised for state space generation
RS_gen_left_syncrules = []
# new syncrules introduced by the rulesystem
RS_right_syncrules = {}
RS_right_syncactions = []
# syncrules in the rulesystem w.r.t. the right-hand patterns, optimised for state space generation
RS_gen_right_syncrules = []
# full list of syncrules for network after transformation
newsyncrules = {}
# full sets of actions for network after transformation
newsyncactions = []
# the concrete actions in the process action sets after transformation subject to synchronisation
#newprocssyncactsets = []

# on which processes does a rule match?
rulematcheson = []
# matches information for all processes, and all rules, from rule state (left pattern) to process states
procsrulematches = []
# COMBINED matches information for all processes, and all rules, from rule state (left pattern) to process states
procsrulestatemaps = []

# a list of checks for property preservation. A check consists of two sets of dependent rule id's (transformation rule id's and add rule id's)
checks = []
# a list of action exclusion sets. For each check, the corresponding exclusion set should be excluded from hiding
exclsets = []

# global variables for compositional model checking
# dependency relation of process LTSs w.r.t. the property LTS (directly dependent LTSs are in first set in list, one step indirectly dependent in the next, etc.
prop_dependency = []
prop_priority = {}
nontrivialpropactions = set([])

# cmc: compositional model checking structures
constraintsLTSs = []
constraintsLTStree = []
basic_constraintsLTSs = []
#min_constraintsLTSs = []
propertyLTSs = []
# sync rules and actions for cmc checks
cmc_syncrules = []
cmc_syncactions = []
# slightly different sync rules and actions for constraints LTS construction (differs in syncs of ACCEPT)
# in cmc_syncrules: i must NOT synchronise on ACCEPT
# in cmc_constraintsconstr_syncrules: i must synchronise on ACCEPT
cmc_constraintsconstr_syncrules = []
cmc_constraintsconstr_syncactions = []
cmc_constraintsdep = []
cmc_checktree = ({},set([]))
cmc_checklist = []
checkprocs = []
checkheaders = []
abstractcheckprocs = []
abstractcheckheaders = []
constraintsupdateprocs = []
constraintsupdateheaders = []
nrchecksshift = 0
# list to keep track of constraints updates to be made
cmc_constraints_updates = []
constraintsLTS_is_extended = []

# class Timer(object):
# 		def __enter__(self):
# 				self.__start = time.time()
# 
# 		def __exit__(self, type, value, traceback):
# 				# Error handling here
# 				self.__finish = time.time()
# 
# 		def duration_in_seconds(self):
# 				return self.__finish - self.__start
# 
# timer = Timer()

def print_error(s):
	"""Print message to screen and exit"""
	if not opt.quiet:
		if config.outputobject == "":
			print("ERROR: " + str(s))
		else:
				config.outputobject.log("ERROR: " + str(s) + "\n")
	if config.outputobject == "":
		sys.exit(1)

def print_message(s):
	"""Print message to screen"""
	if not opt.quiet:
		if config.outputobject == "":
			print(s)
		else:
			config.outputobject.log(str(s) + "\n")

def print_separator():
	"""Print separator to screen"""
	if not opt.quiet and config.outputobject == "":
		print('---')

def toTupleOfTuples(l):
	"""Convert list of lists (depth unknown) to tuple of tuples"""
	if hasattr(l, "__iter__") and not isinstance(l, str):
		return tuple(toTupleOfTuples(x) for x in l)
	else:
		return l

# START PERMUTATIONS WITH UNIQUE VALUES

class unique_element:
	def __init__(self,value,occurrences):
		self.value = value
		self.occurrences = occurrences

def perm_unique(elements):
	eset=set(elements)
	listunique = [unique_element(i,elements.count(i)) for i in eset]
	u=len(elements)
	return perm_unique_helper(listunique,[0]*u,u-1)

def perm_unique_helper(listunique,result_list,d):
	if d < 0:
		yield tuple(result_list)
	else:
		for i in listunique:
			if i.occurrences > 0:
				result_list[d]=i.value
				i.occurrences-=1
				for g in  perm_unique_helper(listunique,result_list,d-1):
					yield g
				i.occurrences+=1

# END PERMUTATIONS WITH UNIQUE VALUES

# BEGIN I/O FUNCTIONS



def addRule(alist):
	global rulefiles
	rulefiles.append((alist[0][1:][:-1], alist[1][1:][:-1], alist[2]))


def parseSet(S):
	"""Parse the given application scope into a set"""
	S = S[1:][:-1]
	S.replace(' ', '')
	slist = S.split(',')
	rset = set([])
	for s in slist:
		rset.add(int(s))
	return rset

def writeMap(folder, filebase):
	"""Write the mapping between system state indices and process state vectors, as established in the hashtable"""
	global hashtable
	
	outfile = open(os.path.join(folder, filebase + ".map"), 'w')
	for v, k in hashtable.items():
		outfile.write(k + ', ' + v + '\n')
	outfile.close()

def readMap(folder, filebase):
	"""Read the mapping between system state indices and process state vectors"""
	global hashtable
	result = {}
	try:
		inFile = open(os.path.join(folder, filebase + ".map"), 'r')
		inFile.close()
	except IOError:
		print_error("the mapping file does not exist!")
	#lines = inFile.readlines()
	for line in open(os.path.join(folder, filebase + ".map")):
		linelist = line.split(', ')
		vlist = linelist[1].split(',')
		vlist[len(vlist)-1] = vlist[len(vlist)-1][:-1]
		result[linelist[0]] = vlist[1:]
	return result

def reverseHashtable():
	"""Reverse the contents of hashtable, and put it in revhashtable"""
	global hashtable, revhashtable
	revhashtable.clear()
	for k, v in hashtable.items():
		revhashtable[v] = k

def readProcndivsets(filebase, propbase):
	"""Read the non-diverging process states from disk"""
	global procndivsets
	try:
		inFile = open(os.path.join(network.folder, filebase + "_" + propbase + ".ndv"), 'rb')
		procndivsets = pickle.load(inFile)
		inFile.close()
	except IOError:
		print_error("the file with non-diverging process states does not exist!")


def writeProcndivsets(filebase, propbase):
	"""Write the non-diverging process states to disk"""
	global procndivsets
	outFile = open(os.path.join(network.folder, filebase + "_" + propbase + ".ndv"), 'wb')
	pickle.dump(procndivsets, outFile)
	outFile.close()

def writeNewProcndivsets(filebase, propbase):
	"""Write the updated non-diverging process states to disk in new file"""
	i = filebase.rfind(".")
	if i == -1:
		newfile = filebase + ".1"
	else:
		version = int(filebase[i+1:])
		newfile = filebase[:i] + "." + str(version+1)
	writeProcndivsets(newfile, propbase)

def readProcsrulestatemaps(filebase, rulebase):
	"""Read procsrulestatemaps info"""
	global procsrulestatemaps
	try:
		inFile = open(os.path.join(network.folder, filebase + "_" + rulebase + ".pmp"), 'rb')
		procsrulestatemaps = pickle.load(inFile)
		inFile.close()
	except IOError:
		print_error("Checks information does not exist! First check for well-formedness and completeness!")


def writeProcsrulestatemaps(filebase, rulebase):
	"""Write procsrulestatemaps info"""
	global procsrulestatemaps
	outFile = open(os.path.join(network.folder, filebase + "_" + rulebase + ".pmp"), 'wb')
	pickle.dump(procsrulestatemaps, outFile)
	outFile.close()

RSscanner=re.Scanner([
	(r"transform",															lambda scanner,token:("SECTIONSTART", 0)),
	(r"add",																	lambda scanner,token:("SECTIONSTART", 1)),
	(r"des",																	lambda scanner,token:("HEADER", token)),
	(r"\[[0-9]+[.[0-9]+]?,[0-9]+[.[0-9]+]?\]",								lambda scanner,token:("COORDS", token)),
	(r"[0-9]+",																lambda scanner,token:("NAT", token)),
	(r"[\s,\(\)]+",															None), # None == skip token.
	(r"->",																	lambda scanner,token:("TO", token)),
	(r"[A-Za-z0-9!\_\-\?.\*]+\([A-Za-z0-9!\_\-\?,.\*\(\)]+\)|[A-Za-z0-9!\_\-\?.\*]+|[\"\'][A-Za-z0-9!\?\_\-\#\s.,\*\(\)]+[\"\']",	lambda scanner,token:("ACTION", token)),
])

syncrulescanner=re.Scanner([
	(r"synch\sleft",															lambda scanner,token:("SECTIONSTART", 2)),
	(r"synch\sright",															lambda scanner,token:("SECTIONSTART", 3)),
	(r"->",																	lambda scanner,token:("TO", token)),
	(r"[A-Za-z0-9!\_\-?.]+|\*|\_",	lambda scanner,token:("ACTION", token)),
	(r"[\{\}\<\>]",					lambda scanner,token:("BRACKET", token)),
	(r"#[0-9]+",						lambda scanner,token:("ARITY", token)),
	(r"[\s,\(\)]+",					None), # None == skip token.
])

# START PERMUTATIONS WITH UNIQUE VALUES ON SPECIFIC POSITIONS

# Permutation function for constructing valid synchronisation rules

# f is a function indicating for each action which positions are valid
# size is the requested size of the vectors (depends on whether we want network or rule system sync rules)
def perm_pos_unique(elements, f, size):
	eset=set(elements)
	# compute possible elements for every vector position
	dom = []
	for i in range(0,size):
		dom.append(set([]))
	for e in eset:
		for i in f.get(e):
			dom[i].add(e)
	# determine where to add *'s
	for i in range(0,len(dom)):
		S = set([])
		totalcount = 0
		for a in dom[i]:
			S |= f.get(a)
			totalcount += elements.count(a)
		if len(S) > totalcount or S == set([]):
			dom[i].add('*')
	listposunique = [unique_element(i,elements.count(i)) for i in eset]
	listposunique.append(unique_element('*',size-len(elements)))
	return perm_pos_unique_helper(listposunique,['*']*size,size-1,dom)

def perm_pos_unique_helper(listposunique,result_list,d,dom):
	if d < 0:
		yield tuple(result_list)
	else:
		for i in listposunique:
			if i.value in dom[d]:
				if i.occurrences > 0:
					result_list[d]=i.value
					i.occurrences-=1
					for g in perm_pos_unique_helper(listposunique,result_list,d-1,dom):
						yield g
					i.occurrences+=1

# END PERMUTATIONS WITH UNIQUE VALUES ON SPECIFIC POSITIONS

def extractPattern(p):
	"""Extract a pattern description (for verification/transformation) from a given process object p"""
	transheader = []
	trans = {}
	actset = set([])
	# we rearrange the header for backwards compatibility
#	htmp = transheader[2]
	# internal header:
	# 0: number of glue-states
	# 1: number of transitions
	# 2: number of states
	# 3: number of exclusive glue-states
	transheader.append(str(len(p.glue_states) + len(p.exclusive_glue_states)))
	transheader.append(str(len(p.transitions)))
	transheader.append(str(len(p.states) + len(p.glue_states) + len(p.exclusive_glue_states)))
	transheader.append(str(len(p.exclusive_glue_states)))
	# count to remove double entries
	ntrans = 0
	#store transitions in memory
	for (tid, t) in p.transitions.items():
		src = str(t["source"]["id"])
		act = str(t["label"])
		tgt = str(t["target"]["id"])
		# remove quotes
		act = act.replace('\'', '')
		act = act.replace('"', '')
		# remove spaces
		act = act.replace(' ', '')
		# put transition label in actset
		actset.add(act)
		# add transition
		outgoing = trans.get(src)
		if outgoing is None:
			outgoing = {}
		outgoingwithlabel = outgoing.get(act)
		if outgoingwithlabel is None:
			outgoing[act] = set([tgt])
			ntrans += 1
		else:
			if tgt not in outgoingwithlabel:
				# insert new element
				outgoingwithlabel.add(tgt)
				outgoing[act] = outgoingwithlabel
				ntrans += 1
		trans[src] = outgoing
	transheader[1] = str(ntrans)
	return [transheader, trans, actset]

def readProcess(l, index):
	"""Read the LTS pattern in list l at index"""
	if l[index][0] != 'HEADER':
		print_error("unexpected start of pattern description!")
	newproc = Process()
	transheader = []
	# a pattern has four values in the header:
	# 0: nr of transitions
	# 1: nr of states
	# 2: nr of glue-states
	# 3: nr of exclusive (out) states
	index += 1
	for j in range(0,4):
		transheader.append(l[index][1])
		index += 1
	# sanity check
	if int(transheader[1]) < int(transheader[2]):
		print_error("the number of states must be >= the number of glue-states!")
	if int(transheader[2]) < int(transheader[3]):
		print_error("the number of glue-states must be >= the number of exclusive glue-states!")
	# possibly read the coords of the states
	read_coords = False
	if l[index][0] == 'COORDS':
		for i in range(0,int(transheader[1])):
			coords = l[index][1].strip('\[\]').split(',')
			if i < int(transheader[3]):
				newproc.add_exclusive_glue_state(float(coords[0]), float(coords[1]))
			elif i < int(transheader[2]):
				newproc.add_glue_state(float(coords[0]), float(coords[1]))
			else:
				newproc.add_state(float(coords[0]), float(coords[1]))
			index += 1
		# read coords in remainder of file
		read_coords = True
	else:
		# add states without coordinates
		for i in range(0,int(transheader[1])):
			if i < int(transheader[3]):
				newproc.add_exclusive_glue_state(0.0, 0.0)
			elif i < int(transheader[2]):
				newproc.add_glue_state(0.0, 0.0)
			else:
				newproc.add_state(0.0, 0.0)
	#store transitions in memory
	currentsrc = ''
	newentry = {}
	while index < len(l):
		if l[index][0] != 'NAT':
			break
		src = l[index][1]
		act = l[index+1][1]
		tgt = l[index+2][1]
		index += 3
		if read_coords:
			coords = []
			coords.append(tuple(l[index][1].strip('\[\]').split(',')))
			coords.append(tuple(l[index+1][1].strip('\[\]').split(',')))
			coords.append(tuple(l[index+2][1].strip('\[\]').split(',')))
			index += 3
		# remove quotes
		act = act.replace('\'', '')
		act = act.replace('"', '')
		# remove spaces
		act = act.replace(' ', '')
		if read_coords:
			newproc.add_transition(int(src), int(tgt), act, float(coords[0][0]), float(coords[0][1]), float(coords[1][0]), float(coords[1][1]), float(coords[2][0]), float(coords[2][1]))
		else:
			newproc.add_transition(int(src), int(tgt), act, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
	return index, newproc

def RS_getRulesWithAction(action, side):
	"""Lookup the rule containing the given action in the left (side==False) or right (side==True) pattern"""
	global RS, RS_add, RS_actprefixsets, RS_ownsaction
	elside = 0
	if side:
		elside = 1
	if action == '*':
		return set([])
	indices = RS_ownsaction[elside].get(action)
	if indices is not None:
		return indices
	indices = set([])
	for i in range(0,len(RS)):
		if action in RS_actprefixsets[i][elside]:
			indices.add(i)
	for i in range(0,len(RS_add)):
		if action in RS_actprefixsets[i+len(RS)][elside]:
			indices.add(len(RS)+i)
	RS_ownsaction[elside][action] = indices
	return indices

def RS_getNewRules(side, type, acts, an):
	"""Create new sync rules for rule system (vector of actions, resulting action, multiset of actions from outside the rule system)"""
	global RS_vector
	posforaction = {}
	interface = Counter()
	elside = 0
	vect = []
	if side:
		elside = 1
	if type == 1:
		# simple rule
		S = RS_getRulesWithAction(acts,side)
		if S == set([]):
			interface[acts] += 1
			return ([], '', interface)
		vect = []
		for i in range(0,int(an)):
			vect.append(acts)
		rltact = acts
	if type == 2 or type == 3:
		# vector rule
		vect = []
		for act in acts:
			if act != '*':
				S = RS_getRulesWithAction(act,side)
				if S == set([]):
					interface[act] += 1
				else:
					vect.append(act)
		rltact = an
	for action in vect:
		positions = posforaction.get(action)
		if positions is None:
			positions = set([])
			indices = RS_ownsaction[elside].get(action)
			for i in range(0,len(RS_vector)):
				if RS_vector[i] in indices:
					positions.add(i)
			posforaction[action] = positions
	tmplist = list(perm_pos_unique(vect, posforaction, len(RS_vector)))
	return (tmplist, rltact, interface)

def preprocessRulesystem():
	"""Convert the 'visual' representation of a rule system to the one used for transformation and verification"""
	global RS, RS_add, RS_vector, RS_left_syncactions, RS_right_syncactions, RS_left_syncrules, RS_right_syncrules, RS_gen_left_syncrules, RS_gen_right_syncrules, newsyncrules, acttmplist
	global token, next, procndivsets

	# clear previous contents
	RS = []
	RS_add = []
	RS_vector = []
	RS_left_syncactions = []
	RS_right_syncactions = []
	RS_left_syncrules = []
	RS_right_syncrules = []
	RS_gen_left_syncrules = []
	RS_gen_right_syncrules = []
	procndivsets = []

	for rid, pats in config.rules_and_processes.items():
		if rid.find('Transform') != -1:
			# a transformation rule to process
			lpattern = extractPattern(pats.left)
			rpattern = extractPattern(pats.right)
			# add the rule to the rule system in memory
			# THIRD ELEMENT IS NOW AN EMPTY SET! PLACEHOLDER FOR APPLICATION SCOPES!!!
			RS.append((lpattern, rpattern, set([])))
		else:
			# an add rule to read
			lpattern = [['1', '0', '1', '1'], {}, set([])]
			rpattern = extractPattern(pats)
			# add the rule to the rule system in memory
			# application scope is chosen later to add appropriate number of new processes (w.r.t. new synch rules)
			RS_add.append((lpattern, rpattern, set([])))
	# per rule, store the action prefixes of left and right patterns in sets
	for i in range(0,len(RS)):
		RS_actprefixsets.append([set([]),set([])])
		for a in RS[i][0][2]:
			RS_actprefixsets[i][0].add(action.stripParams(a))
		for a in RS[i][1][2]:
			RS_actprefixsets[i][1].add(action.stripParams(a))
	for i in range(0,len(RS_add)):
		RS_actprefixsets.append([set([]),set([])])
		for a in RS_add[i][1][2]:
			RS_actprefixsets[i+len(RS)][1].add(action.stripParams(a))

	# read the remainder of the input, containing sync rules
	l = []
	input = 'synch left\n' + config.existing_synchronisation_rules + 'synch right\n' + config.new_synchronisation_rules
	lines = input.split('\n')
	for lx2 in range(0,len(lines)):
		results, remainder = syncrulescanner.scan(lines[lx2])
		l += results + [('NEWLINE',0)]
	index = 0
	section = l[index][1]
	index += 2
	process_rules = False

	# process the new syncrules
	# as we do this, we keep track of how many elements we will need to have for the verification of the rule system
	# (depends on the syncrules)
	required_rulevector_elements = Counter()
	for i in range(0,len(RS)):
		required_rulevector_elements[i] += 1
	for i in range(0,len(RS_add)):
		required_rulevector_elements[len(RS)+i] += 1
	tmp_rs_syncrules = set([])
	for j in [0,1]:
		sync_law.reset()
		sync_law.tmpsynccounter = 0
		while index < len(l):
			skipline = False
			if l[index][0] == 'NEWLINE':
				skipline = True
				index += 1
			else:
				if l[index][0] == 'SECTIONSTART':
					index += 1
					break
				rules_seen = copy.deepcopy(required_rulevector_elements)
				if l[index][0] == 'BRACKET':
					vect = '(' + l[index][1]
					index += 1
					while l[index][0] != 'BRACKET':
						act = l[index][1]
						vect += act
						# check rules_seen
						rids = RS_getRulesWithAction(act, section==3)
						for rid in rids:
							if rules_seen[rid] > 0:
								rules_seen[rid] -= 1
							else:
								required_rulevector_elements[rid] += 1
						if l[index+1][0] != 'BRACKET':
							vect += ','
						index += 1
					vect += l[index][1] + ',' + l[index+1][1] + ')'
					index += 2
				else:
					# we have a rule of type a #n OR a rule in the format a b c -> d
					act = l[index][1]
					index += 1
					arity_rule = False
					if index == len(l):
						arity = 2
						arity_rule = True
					else:
						if l[index][0] == 'ARITY':
							arity = int(l[index][1][1:])
							arity_rule = True
						else:
							if l[index][0] == 'NEWLINE':
								arity = 2
								arity_rule = True
							else:
								# format a b c -> d
								vect = '({' + act
								# check rules_seen
								rids = RS_getRulesWithAction(act, section==3)
								for rid in rids:
									if rules_seen[rid] > 0:
										rules_seen[rid] -= 1
									else:
										required_rulevector_elements[rid] += 1
								while l[index][0] != 'TO':
									act = l[index][1]
									vect += ',' + act
									rids = RS_getRulesWithAction(act, section==3)
									for rid in rids:
										if rules_seen[rid] > 0:
											rules_seen[rid] -= 1
										else:
											required_rulevector_elements[rid] += 1
									index += 1
								index += 1
								# add result of rule
								vect += '},' + l[index][1] + ')'
								index += 1
					if arity_rule:
						rids = RS_getRulesWithAction(act, section==3)
						if rids != set([]):
							for rid in rids:
								if rules_seen[rid] >= arity:
									rules_seen[rid] -= arity
								else:
									required_rulevector_elements[rid] += (arity-rules_seen[rid])
									rules_seen[rid] = 0
						vect = act + ' #' + str(arity)
						index += 1
			if not skipline:
				(type, acts, an) = sync_law.parse(vect)
				tmp_rs_syncrules.add((section==3, type, acts, an))

		if section == 2:
			section = 3
	# all syncrules have been obtained. rewrite them to required vectors
	# construct RS_vector
	for i in range(0,len(RS)):
		for j in range(0,required_rulevector_elements[i]):
			RS_vector.append(i)
	for i in range(0,len(RS_add)):
		for j in range(0,required_rulevector_elements[len(RS)+i]):
			RS_vector.append(len(RS)+i)

	RS_left_syncrules = []
	RS_right_syncrules = []
	for (side, type, acts, an) in tmp_rs_syncrules:
		newrules = RS_getNewRules(side, type, acts, an)
		if not side:
			RS_left_syncrules.append(newrules)
		else:
			RS_right_syncrules.append(newrules)

	# if the interface of a syncrule is non-empty, we rename the action resulting from that rule to make it unique
	counter = 0
	tmp = []
	for (vects, rltact, interface) in RS_left_syncrules:
		if len(list(interface.elements())) > 0:
			tmp.append((vects, rltact + "_itf" + str(counter), interface))
			counter += 1
		else:
			tmp.append((vects, rltact, interface))
	RS_left_syncrules = tmp
	tmp = []
	for (vects, rltact, interface) in RS_right_syncrules:
		if len(list(interface.elements())) > 0:
			tmp.append((vects, rltact + "_itf" + str(counter), interface))
			counter += 1
		else:
			tmp.append((vects, rltact, interface))

	tmp_rs_syncrules = storeRulesInDict(RS_left_syncrules)
	RS_left_syncactions = sync_law.buildSyncactionsets(tmp_rs_syncrules, len(RS_vector))

	# order the rules in a list of dictionaries for the generation of LTSs of right hand rule patterns
	RS_gen_left_syncrules = []
	for i in range(0,len(RS_vector)):
		RS_gen_left_syncrules.append({})
	RS_gen_left_syncrules = sync_law.orderSyncrules(tmp_rs_syncrules, RS_gen_left_syncrules)

	tmp_rs_syncrules = storeRulesInDict(RS_right_syncrules)
	RS_right_syncactions = sync_law.buildSyncactionsets(tmp_rs_syncrules, len(RS_vector))

	RS_gen_right_syncrules = copy.deepcopy(RS_gen_left_syncrules)
	RS_gen_right_syncrules = sync_law.orderSyncrules(tmp_rs_syncrules, RS_gen_right_syncrules)

	# CHECK MODEL INDEPENDENT WELL-FORMEDNESS OF SYNC RULES
	# Check if existing sync actions occurring in right patterns also appear in corresponding left ones
	for i in range(0,len(RS)):
		for a in RS[i][1][2]:
			if mustSync(a, i, RS_left_syncactions):
				# does the same action also exist in left pattern?
				if a not in RS[i][0][2]:
					print_error("well-formedness violated! Transformation rule " + str(i) + " uses an existing sync action in the right pattern that is not in the left pattern!")
	for i in range(0,len(RS_add)):
		for a in RS_add[i][1][2]:
			if mustSync(a, i, RS_left_syncactions):
				print_error("well-formedness violated! Add rule " + str(i) + " uses existing sync action " + str(a) + " in its pattern!")

	for i in range(0,len(RS_vector)):
		RS_right_syncactions[i] |= RS_left_syncactions[i]

	# Possibly extend the network with positions for newly added processes
	if network.name != "":
		# convert the input network to the new size
		# add application scopes to the add rules and merge them with RS
		current = len(network.procs)
		network.inputnetwork += [i for i in range(len(network.procs),len(network.procs)+len(RS_add))]
		RS_add_tmp = []
		for i in range(0,len(RS_add)):
			RS_add_tmp.append((RS_add[i][0], RS_add[i][1], set([current+j for j in range(0,required_rulevector_elements[len(RS)+i])])))
			current += required_rulevector_elements[len(RS)+i]
		RS_add = RS_add_tmp
		for i in range(0,len(RS_add)):
			network.procsheaders.append(['0','0','1'])
			network.procsactsets.append(set([]))
			network.procsactprefixsets.append(set([]))
			network.syncactions.append(set([]))
			network.procs.append({})
		# extend the syncrules
		extendedrules = []
		for rsi in range(0,len(network.syncrules)):
			extendedrules.append({})
			for a, v in network.syncrules[rsi].items():
				out = []
				for (vect,an) in v:
					out.append((sync_law.extendVector(vect, 0, network.inputnetwork),an))
				extendedrules[rsi][a] = out
		for rsi in range(0,len(RS_add)):
			extendedrules.append({})
		network.syncrules = extendedrules
# 	print(RS_left_syncactions)
# 	print(RS_left_syncrules)
# 	print(RS_right_syncactions)
# 	print(RS_right_syncrules)
# 	print(RS)

def readRulesystem(filename):
	"""Read a rule system, which contains pairs of LTSs, newly to be added LTSs, and synchronisation rules"""
	lines = []
	try:
		inFile = open(filename + ".rs",'r')
		lines = inFile.readlines()
		inFile.close()
	except IOError:
		print_error("rule system file does not exist!")

	l = []
	for lx in range(0,len(lines)):
		if lines[lx].find('synch left') != -1 or lines[lx].find('synch right') != -1:
			break
		results, remainder = RSscanner.scan(lines[lx])
		l += results
	index = 0
	section = 0
	# counter to id rules and processes
	idcounter = 0
	while index < len(l):
		if l[index][0] == 'SECTIONSTART':
			section = l[index][1]
			index += 1
		else:
			if section == 0:
				# a transformation rule to read
				index, lProcess = readProcess(l, index)
				if l[index][0] != 'TO':
					print_error("unexpected format in rule system file!")
				index += 1
				index, rProcess = readProcess(l, index)
				# add the rule to the rule system in memory
				r = Rule()
				r.setPatterns(lProcess, rProcess)
				config.rules_and_processes["Transformation " + str(idcounter)] = r
				idcounter += 1
			if section == 1:
				# an add rule to read (i.e. process)
				index, rProcess = readProcess(l, index)
				# add the rule to the rule system in memory
				config.rules_and_processes["Process " + str(idcounter)] = rProcess
				idcounter += 1
	# read the remainder of the input, containing sync rules
	l = []
	gui_syncrules = ["",""]
	mode = 0
	for lx2 in range(lx,len(lines)):
		if lines[lx2] == 'synch left\n':
			mode = 0
		elif lines[lx2] == 'synch right\n':
			mode = 1
		else:
			gui_syncrules[mode] += lines[lx2]
	config.existing_synchronisation_rules = gui_syncrules[0]
	config.new_synchronisation_rules = gui_syncrules[1]

# END I/O FUNCTIONS

# START CONSTRUCT HIDING SET FROM MCL PROPERTY

scanner=re.Scanner([
	(r"[\'\"][A-Za-z\s0-9!.\*\(\),]+[\'\"]", lambda scanner,token:("ACTION", token)),
	(r"true|false",                          lambda scanner,token:("CONST", token)),
	(r"not|or|and|mu|nu|[.\?\*\@]|-\|",      lambda scanner,token:("OPERATOR", token)),
	(r"[A-Z]",                               lambda scanner,token:("VARIABLE", token)),
	(r"[\(\[\<]",                            lambda scanner,token:("OPENBR", token)),
	(r"[\)\]\>]",                            lambda scanner,token:("CLOSBR", token)),
	(r"\s+", None), # None == skip token.
])

def ActSetsUnion(sign1, set1, sign2, set2):
	"""Obtain the union of the two sets"""
	if sign1 == '+':
		if sign2 == '+':
			return ['+', set1 | set2]
		else:
			return ['-', set2 - set1]
	else:
		if sign2 == '+':
			return ['-', set1 - set2]
		else:
			return ['-', set1 & set2]

def combineActSets(l, r, op):
	"""Combine the given actsets"""
	#print 'combine ' + str(l) + ' ' + str(r) + ' with ' + str(op)
	if op == '':
		if not l[0]:
			if not r[0]:
				return l
			else:
				return r
		else:
			if not r[0]:
				return l
			else:
				result = ActSetsUnion(l[1], l[2], r[1], r[2])
				return [True, result[0], result[1]]
	else:
		if op == 'or' or op == 'and':
			if not l[0]:
				if not r[0]:
					result = ActSetsUnion(l[1], l[2], r[1], r[2])
					return [False, result[0], result[1]]
				else:
					return r
			else:
				if not r[0]:
					return l
				else:
					result = ActSetsUnion(l[1], l[2], r[1], r[2])
					return [True, result[0], result[1]]
		else:
			# op == '?'
			if not l[0]:
				return r
			else:
				result = ActSetsUnion(l[1], l[2], r[1], r[2])
				return [True, result[0], result[1]]

def getNonHidingSet(l,mode):
	"""Extract non-hiding set from given list starting at position pos"""
	# if we encounter an opening bracket, do a recursive call for that subterm
	# break the given list l down into subterms
	subl = []
	i = 0
	while i < len(l):
		if l[i][0] == 'OPENBR':
			passl = []
			if l[i][1] == '[' or l[i][1] == '<':
				submode = True
			else:
				submode = False
			brc = 1
			while brc > 0:
				i += 1
				if l[i][0] == 'OPENBR':
					brc += 1
				else:
					if l[i][0] == 'CLOSBR':
						brc -= 1
				if brc > 0:
					passl.append(l[i])
			subl.append([submode,'nest',passl])
		else:
			while l[i][0] != 'OPENBR':
				subl.append([False,'leaf',l[i]])
				i += 1
				if i == len(l):
					break
			i -= 1
		i += 1
	# for each subterm in subl, get the result
	results = []
	for s in subl:
		if s[1] == 'nest':
			results.append(getNonHidingSet(s[2],s[0]))
		else:
			if s[2][0] == 'CONST' or s[2][0] == 'VARIABLE':
				results.append([False,'+',set([])])
			if s[2][0] == 'OPERATOR':
				results.append([False,'op',s[2][1]])
			else:
				if s[2][0] == 'ACTION':
					if s[2][1] == 'tau':
						results.append([False,'-', {'tau'}])
					else:
						results.append([False,'+', {s[2][1]}])
	# combine the subresults
	#print results
	tmpresult = []
	tmpop = ''
	for i in range(0,len(results)):
		if results[i][1] == 'op':
			if results[i][2] == 'or' or results[i][2] == 'and' or results[i][2] == '?' or results[i][2] == '.':
				tmpop = results[i][2]
		else:
			if not tmpresult:
				tmpresult = results[i]
			else:
				tmpresult = combineActSets(tmpresult, results[i], tmpop)
				tmpop = ''
	if mode:
		return [True, tmpresult[1], tmpresult[2]]
	else:
		return tmpresult

def constructHidingSet():
	"""Read the property in propertyfile and construct hiding set"""
	global hideactions
	lines = []
	try:
		propertyfile = open(os.path.join(config.property_folder, config.property_name + ".mcl"), 'r')
		lines = propertyfile.readlines()
		propertyfile.close()
	except IOError:
		print_error("property file does not exist!")


	prop = ""
	for line in lines:
		prop += line.rstrip()
	global token, next
	results, remainder = scanner.scan(prop)
	nhset = getNonHidingSet(results,False)
	#print nhset
	if not nhset[0]:
		hideactions.append('all')
	else:
		if nhset[1] == '+':
			hideactions.append('all')
			if nhset[2] != set([]):
				hideactions.append('but')
				for a in nhset[2]:
					hideactions.append(a)
		else:
			if nhset[2] == set([]):
				hideactions.append('none')
			else:
				for a in nhset[2]:
					hideactions.append(a)
	writeHideActions()

# END CONSTRUCT HIDING SET FROM MCL PROPERTY

def getSubsystem(i, l):
	"""Get the subsystem at position i in l"""
	if hasattr(l[i], "__iter__") and not isinstance(l[i], str):
		return l[i]
	else:
		return [l[i]]

def getMatchedActions(a, statemap, i):
	"""get the set of concrete actions on which action a in transformation rule i matches; interprets placeholders"""
	global RS
	rset = set([])
	t = a.split('#')
	if len(t) > 1:
		for m in statemap:
			ac = action.rename(a, m[1])
			rset.add(ac)
	else:
		rset.add(a)
	return rset

def storeRulesInDict(rules):
	"""Put the list of rules in a dictionary sorted by resulting action"""
	result = {}
	for r in rules:
		rlt = result.get(r[1])
		if rlt is None:
			rlt = []
		for vect in r[0]:
			rlt.append(vect)
		if rlt:
			result[r[1]] = rlt
	return result

def getRevTrans(trans):
	"""store the reversed LTS"""
	revtrans = {}
	for k, v in trans.items():
		for a, t in v.items():
			for tgt in t:
				# reversed procs
				incoming = revtrans.get(tgt)
				if incoming is None:
					revtrans[tgt] = {a: {k}}
				else:
					incomingwithlabel = incoming.get(a)
					if incomingwithlabel is None:
						incoming[a] = {k}
					else:
						if k not in incomingwithlabel:
							incomingwithlabel.add(k)
						incoming[a] = incomingwithlabel
					revtrans[tgt] = incoming
	return revtrans

def getActTrans(trans):
	"""store the LTS sorted by transition labels"""
	atrans = {}
	for k, v in trans.items():
		for a, t in v.items():
			for tgt in t:
				# action procs
				tr = atrans.get(a)
				if tr is None:
					atrans[a] = {k: {tgt}}
				else:
					trwithk = tr.get(k)
					if trwithk is None:
						tr[k] = {tgt}
					else:
						if tgt not in trwithk:
							trwithk.add(tgt)
							tr[k] = trwithk
					atrans[a] = tr
	return atrans

# BEGIN functions for transformation rules / performing transformations on a network

def checkConfluence():
	"""Check confluence and termination of the rulesystem; simple check on action sets"""
	# for confluence, we check that the left hand action sets of the rules are disjoint
	# NOTE: this is check 1 for confluence. Check 2 is done when matches are determined.
	# For this, see function checkMatchesIntersect()
	#leftunion = set([])
	for i in range(0,len(RS)):
		#leftunion = leftunion | ((RS[i])[0])[2]
		for j in range(i+1,len(RS)):
			if len(((RS[i])[0])[2] & ((RS[j])[0])[2]) > 0:
				print_message(str(RS[i][0][2]))
				print_message(str(RS[j][0][2]))
				print_error("rules " + str(RS[i]) + "and " + str(RS[j]) + " are not confluent!")

def checkMatchesIntersect(rule, mapinfo, statemap):
	"""Perform check 2 for confluence: no two matches of a rule intersect"""
	# Check that no two states match on the same state
	# This is ok if the two states relate to a glue state, and
	# they have no conflicting transitions, i.e. they do not have
	# an incoming or outgoing transition in common
	intersected = set([])
	set1union = set([])
	set2union = set([])
	# function mapping process states to match ids. TD required to determine that no transitions are shared
	map_proc_to_mtch = {}	
	# get reversed LTS
	revtrans = getRevTrans(rule[0][1])
	for i in range(0,int(rule[0][0][2])):
		intertmp = set1union & mapinfo.get(str(i))
		intersected = intersected | intertmp
		set1union = set1union | mapinfo.get(str(i))
	# Now we have in intersected the set of process states that are matched on multiple times
	# Check per member if we ever have an overlap in ingoing and outgoing transitions
	set1union = set([])
	for s in intersected:
		for i in range(int(rule[0][0][0]),int(rule[0][0][2])):
			# TO FIX!
			if s in mapinfo.get(str(i)):
				# overlap?
				transset = rule[0][1].get(s)
				if transset is None:
					transset = {}
				for a, v in transset.items():
					if a in set1union:
						print_error("ERROR: Intersecting matches detected. Rule " + str(rule) + " is not confluent!")
					set1union.add(a)
				transset = revtrans.get(s)
				if transset is None:
					transset = {}
				for a, v in transset.items():
					if a in set2union:
						print_error("Intersecting matches detected. Rule " + str(rule) + " is not confluent!")
					set2union.add(a)

def getNumberOfOutgoing(trans):
	"""Retrieve the number of transitions in trans"""
	number = 0
	if trans is not None:
		for (a,v) in trans:
			number += len(v)
	return number
			
def transformProcess(id):
	"""transform the given process according to the established matches"""
	global transformed_procs, transformed_procsheaders, transformed_procs_new_states, procndivsets, RS, RS_add, procsrulematches
	transformed_procs[id] = copy.deepcopy(network.procs[id])
	transformed_procsheaders[id] = (network.procsheaders[id][0], network.procsheaders[id][1], network.procsheaders[id][2])
	nstates = int((network.procsheaders[id])[2])
	statecounter = nstates
	ntrans = int((network.procsheaders[id])[1])
	deleted = deque([])
	newmtch = {}
	transformed = False
	# in this list, we store for each process a mapping for each rule from new states to process states (right hand patterns)
	newstatesmaps = []
	count = 0
	for rid in range(0,len(procsrulematches[id])):
		mapdict = {}
		for mtch in procsrulematches[id][rid]:
			if rid >= len(RS):
				index = rid - len(RS)
				RSYS = RS_add
			else:
				index = rid
				RSYS = RS
			if mtch[0] != {}:
				count += 1
				if not transformed:
					print_message("refining process " + str(id))
				transformed = True
				# update nr of trans
				ntrans += int(RSYS[index][1][0][1]) - int(RSYS[index][0][0][1])
				# delete states
				for i in range(int(((RSYS[index][0])[0])[0]), int(((RSYS[index][0])[0])[2])):
					smap = mtch[0].get(str(i))
					nstates -= 1
					deleted.append(smap)
					(transformed_procs[id]).pop(smap)
				# add new states
				for i in range(int(((RSYS[index][1])[0])[0]), int(((RSYS[index][1])[0])[2])):
					if len(deleted) > 1:
						newmtch[str(i)] = deleted.popleft()
					else:
						newmtch[str(i)] = str(statecounter)
						statecounter += 1
					nstates += 1
					rlt = mapdict.get(str(i))
					if rlt is None:
						rlt = set([])
					rlt.add(newmtch[str(i)])
					mapdict[str(i)] = rlt
				for i in range(int(((RSYS[index][1])[0])[0]), int(((RSYS[index][1])[0])[2])):
					smap = newmtch[str(i)]
					newtrans = {}
					trans = ((RSYS[index][1])[1]).get(str(i))
					if trans is not None:
						for a, v in trans.items():
							newv = set([])
							for tgt in v:
								if int(tgt) < int(RSYS[index][1][0][0]):
									newv.add(mtch[0].get(tgt))
								else:
									newv.add(newmtch.get(tgt))
							concrete_a = action.rename(a, mtch[1])
							newtrans[concrete_a] = newv
							(transformed_procs[id])[smap] = newtrans
				# apply changes to glue state transitions
				for i in range(0, int(((RSYS[index][0])[0])[0])):
					smap = mtch[0].get(str(i))
					out = (transformed_procs[id]).get(smap)
					outpattern = ((RSYS[index][0])[1]).get(str(i))
					if out is None:
						out = {}
					if outpattern is None:
						outpattern = {}
					# remove the transitions in the left hand pattern
					for a, v in outpattern.items():
						# remove the equivalent transitions in the process LTS
						concrete_a = action.rename(a, mtch[1])
						outwithlabel = out.get(concrete_a)
						for tgt in v:
							tmap = mtch[0].get(tgt)
							outwithlabel.remove(tmap)
						out[concrete_a] = outwithlabel
					# add the transitions in the right hand pattern
					outpattern = ((RSYS[index][1])[1]).get(str(i))
					if outpattern is not None:
						for a, v in outpattern.items():
							concrete_a = action.rename(a, mtch[1])
							outwithlabel = out.get(concrete_a)
							if outwithlabel is None:
								outwithlabel = set([])
							newv = set([])
							for tgt in v:
								if int(tgt) < int(((RSYS[index][1])[0])[0]):
									tmap = mtch[0].get(tgt)
								else:
									tmap = newmtch.get(tgt)
								newv.add(tmap)
							out[concrete_a] = outwithlabel | newv
					(transformed_procs[id])[smap] = out
		newstatesmaps.append(mapdict)
	# all rules have been applied; shift the state indices and rewrite to remove gaps
	# also shift state indices in procndivsets[i] and remove deleted indices
	if transformed:
		imap = {}
		cnt = 0
		skip = '-1'
		newndivs = set([])
		for i in range(0,statecounter):
			if deleted != deque([]) and skip == '-1':
				skip = deleted.popleft()
			if str(i) != skip:
				imap[str(i)] = str(cnt)
				if opt.divergency:
					if str(i) in procndivsets[id]:
						newndivs.add(str(cnt))
				cnt += 1
			else:
				skip = '-1'
		if opt.divergency:
			procndivsets[id] = newndivs
		# use new indexing in procs structure
		nprocs = {}
		for src, v in transformed_procs[id].items():
			nprocs[imap[src]] = {}
			for a, t in v.items():
				(nprocs[imap[src]])[a] = set([])
				for tgt in t:
					((nprocs[imap[src]])[a]).add(imap[tgt])
		transformed_procs[id] = nprocs
		# store the new header for the LTS
		transformed_procsheaders[id] = ('0', str(ntrans), str(nstates))
		# use new indexing in newstatesmaps
		for i in range(0,len(procsrulematches[id])):
			nmaps = {}
			for src, v in newstatesmaps[i].items():
				nmaps[src] = set([])
				for sm in v:
					nmaps[src].add(imap[sm])
			newstatesmaps[i] = nmaps
		# store globally
		transformed_procs_new_states.append(newstatesmaps)

def transform():
	global transformed_procs, transformed_procsheaders
	for i in range(0,len(network.procs)):
		transformed_procs.append({})
		transformed_procsheaders.append(())
	for i in range(0,len(network.procs)):
		transformProcess(i)

def getMatchesForProcess(processid):
	"""get the matches for the given process LTS according to the rule system"""
	global RS, RS_add, procsrulestatemaps, procsrulematches, rulematcheson
	rulestatemap = []
	print_message("determining matches in process " + str(processid))
	for rid in range(0,len(RS)):
		# ACTUALLY ADD?
		# determine that the set of sync actions of left pattern of rule rid is equal to the intersection of the set of sync actions
		# of the process LTS and set of actions of the left pattern. In other words, we only match a rule on a process iff the syncactions
		# in the pattern are actually also sync actions in the process.
		statemap = []
		if RS[rid][2] == set([]) or processid in RS[rid][2]:
			statemap = getAllMatches(processid, RS[rid])
			# the set of deleted states contains all states with an index >= first number in headers of rule
			statemap = removeDanglingMatches(processid, RS[rid], statemap)
			statemap = removeExclusiveglueViolations(processid, RS[rid], statemap)
		rulestatemap.append(statemap)
	# add special entries for add rules
	for rid in range(0,len(RS_add)):
		if processid in RS_add[rid][2]:
			rulestatemap.append([[{'0': '0'},{}]])
		else:
			rulestatemap.append([])
	# procsrulestatemaps is used to keep for all processes and all rules the mappings from left pattern states to process states
	# This is used later when updating the non-divergency sets (divergency of process states must be carried over to rule states)
	# procsrulematches is a list of matches for each process, each rule
	procsrulematches.append(rulestatemap)
	tmp = []
	for rid in range(0,len(RS)):
		mapinfo = groupMatches(rulestatemap[rid])
		# perform check 2 for confluence check: no two matches intersect
		if mapinfo != {}:
			checkMatchesIntersect(RS[rid], mapinfo, rulestatemap[rid])
		tmp.append(mapinfo)
	procsrulestatemaps.append(tmp)

def matchRulesystem():
	"""Determine all matches of rules on processes"""
	global revprocs, procsrulestatemaps, procsrulematches, rulematcheson, RS_add
	actprocs = []
	revprocs = []
	for i in range(0,len(network.procs)):
		rlt = getActTrans(network.procs[i])
		actprocs.append(rlt)
		rlt = getRevTrans(network.procs[i])
		revprocs.append(rlt)
	procsrulestatemaps = []
	procsrulematches = []
	for i in range(0,len(network.procs)):
		getMatchesForProcess(i)
	# build list indicating on which processes a rule is applicable
	rulematcheson = []
	for rid in range(0,len(RS)):
		tmp = set([])
		for pid in range(0,len(procsrulematches)):
			if procsrulematches[pid][rid]:
				tmp.add(pid)
		rulematcheson.append(tmp)
	for rid in range(0,len(RS_add)):
		rulematcheson.append(RS_add[rid][2])

def matchSyncrules():
	"""Match the syncrules (old and new) of the rulesystem on the network"""
	global RS, RS_vector, newsyncrules, procsrulestatemaps, procsrulematches, newsyncactions, RS_left_syncrules
	global RS_right_syncrules, RS_ownsaction, rulematcheson, RS_actprefixsets
	structureset = []
	#for i in range(0,len(network.inputnetwork)):
	#	if hasattr(network.inputnetwork[i], "__iter__") and not isinstance(network.inputnetwork[i], str):
	#		print network.inputnetwork
	#		structureset.append(set(network.inputnetwork[i]))
	#	else:
	#		structureset.append(set([network.inputnetwork[i]]))
	#posset = {}
	#for i in range(0,len(procsrulematches)):
	#	for j in range(0,len(structureset)):
	#		if i in structureset[j]:
	#			posset[i] = j
	# check compatibility between left syncrules and syncrules of network
	# iterate over action prefixes in left patterns of transformation rules
	seen = set([])
	for i in range(0,len(RS_vector)):
		r = RS_vector[i]
		if r not in seen:
			seen.add(r)
			for a in RS_actprefixsets[r][0]:
				# determine synchronisation possibilities of a
				synchs_a = set([])
				for (vects, rltact, interface) in RS_left_syncrules:
					tmplist = []
					for v in vects:
						if v[i] == a:
							for j in range(0,len(v)):
								if v[j] != '*':
									tmplist.append(v[j])
							break
					if tmplist:
						for ac in list(interface.elements()):
							for j in range(0,interface[ac]):
								tmplist.append(ac)
						tmplist.sort()
						synchs_a.add((tuple(tmplist), action.stripInterfacecounter(rltact)))
				# for all processes matched on by r, check that a has the same synching potential
				for pid in rulematcheson[r]:
					for j in range(0,len(network.syncrules)):
						for ac, v in network.syncrules[j].items():
							for (vect, rltact) in v:
								if vect[pid] == a:
									tmplist = []
									for k in range(0,len(vect)):
										if vect[k] != '*':
											tmplist.append(vect[k])
									if len(tmplist) > 1:
										tmplist.sort()
										if (tuple(tmplist),action.stripInterfacecounter(rltact)) not in synchs_a:
											print_error("action " + str(a) + " has different synching potential in process " + str(pid) + " than in rule " + str(r) + "!")
	# Determine how to translate the RS right syncrules to new concrete network rules
	# Construct concrete sync rules from the RS right syncrules
	f = {}
	for (vects, rltact, interface) in RS_right_syncrules:
		for v in vects:
			for i in range(0,len(v)):
				if v[i] != '*':
					if f.get(v[i]) is None:
						tmp = set([])
						rls = RS_ownsaction[1].get(v[i])
						for r in rls:
							tmp |= rulematcheson[r]
						f[v[i]] = tmp
		intset = set(interface.elements())
		for a in intset:
			if f.get(a) is None:
				tmp = set([])
				for i in range(0,len(network.syncactions)):
					# NOTE: If a does not appear in any syncactions[i], the given interface was not valid.
					# We decide not to act on this; if after verification, the RS is correct with respect
					# to a more restricting interface, then it will definitely be correct with a less restricting
					# one.
					if a in network.syncactions[i]:
						tmp.add(i)
				f[a] = tmp
	matched_rules = {}
	for (vects, rltact, interface) in RS_right_syncrules:
		intset = set(interface.elements())
		for v in vects:
			newvect = []
			for i in range(0,len(v)):
				if v[i] != '*':
					newvect.append(v[i])
			for a in intset:
				for i in range(0,interface[a]):
					newvect.append(a)
			tmplist = list(perm_pos_unique(newvect, f, len(procsrulematches)))
			inttmplist = [(t,(intset != set([]))) for t in tmplist]
			newact = action.stripInterfacecounter(rltact)
			if matched_rules.get(newact) is None:
				matched_rules[newact] = []
			rlt = matched_rules.get(newact)
			matched_rules[newact] = list(set(rlt) | set(inttmplist))
	# filter out invalid vectors, based on existing sync rules of input network, in cases that the interface is not empty
	for a, vects in matched_rules.items():
		newvects = []
		for (v, interface_is_not_empty) in vects:
			if interface_is_not_empty:
				# count the number of actions in the vector related to 'old' processes (i.e. not newly added ones)
				count = 0
				for i in range(0,network.procs_orig_size):
					if v[i] != '*':
						count += 1
				if count <= 1:
					# at most one old process involved. This is correct by definition. (No syncing within the old part of the system)
					found = True
				else:
					# construct list of sets of rules applicable on each process
					apprules = []
					for i in range(0,len(v)):
						if v[i] != '*':
							apprules.append(RS_getRulesWithAction(v[i],True))
						else:
							apprules.append(set([]))
					# We need to be able to find a matching rule in syncrules
					found = False
					for j in range(0,len(network.syncrules)):
						for sr_a, sr_v in network.syncrules[j].items():
							for (v2, rltact) in sr_v:
								for i in range(0,len(v)):
									if v[i] != '*':
										if v[i] in network.procsactprefixsets[i]:
											if v[i] != v2[i]:
												break
										else:
											# new action. determine whether a matching rule has v2[i] in left pattern
											rulefound = False
											for rule in apprules[i]:
												# if rule is an add rule, and v2[i] == '*', we have a match
												if rule > len(RS) and v2[i] == '*':
													rulefound = True
													break
												else:
													if v2[i] in RS_actprefixsets[rule][0]:
														rulefound = True
														break
											if not rulefound:
												break
									if i == len(v)-1:
										found = True
								if found:
									break
							if found:
								break
						if found:
							break
				if found:
					# match found. v is allowed for the network
					newvects.append(v)
			else:
				# interface is empty, rule can be safely added
				newvects.append(v)
		# add newvects to matched_rules
		matched_rules[a] = newvects
		# Possibly warn about filtering
		if not newvects:
			print_message("WARNING!: a new sync right rule has been removed due to inapplicability!")
	# Construct the newsyncactions
	newsyncactions = copy.deepcopy(network.syncactions)
	for ac, vects in matched_rules.items():
		for v in vects:
			for i in range(0,len(v)):
				if v[i] != '*':
					newsyncactions[i].add(v[i])
	newsyncrules = copy.deepcopy(network.syncrules)
	newsyncrules = sync_law.orderSyncrules(matched_rules, newsyncrules)

	# 2. CHECK MODEL DEPENDENT WELL-FORMEDNESS OF SYNC RULES
	# Check if existing sync actions occurring in right patterns also appear in corresponding left ones
	for i in range(0,len(RS)):
		pids = rulematcheson[i]
		for a in RS[i][1][2]:
			for pid in pids:
				if a in network.procsactsets[pid]:
				#if mustSync(a, pid, network.syncactions):
					# does the same action also exist in left pattern?
					if a not in RS[i][0][2]:
						print_error("well-formedness violated! Transformation rule " + str(i) + " applied on process " + str(pid) + " uses an existing action in the right pattern that is not in the left pattern!")
	# 3. CHECK CONSISTENT TRANSFORMATION OF SYNC ACTIONS
	# a data structure to track per process and per rule which concrete sync action labels are matched on
	procsruleconcretesyncactions = []
	for i in range(0,len(network.procs)):
		procsruleconcretesyncactions.append([])
		for j in range(0,len(RS)):
			procsruleconcretesyncactions[i].append(set([]))
	for j in range(0,len(RS)):
		for i in range(0,len(network.procs)):
			mapinfo = procsrulestatemaps[i][j]
			# for all syncing actions in process i occurring in the left-hand pattern, check the matches
			if mapinfo != {}:
				# obtain action ordered left pattern
				actleft = getActTrans((RS[j][0])[1])
				#for a in procssyncactsets[i]:
					#print procssyncactsets[i]
				for a in RS[j][0][2]:
					#if a in (rule[0])[2]:
						#print actprocs[i]
					a_stripped = action.stripParams(a)
					if a_stripped in network.syncactions[i]:
						# obtain a set of concrete action labels on which the pattern action label a applies (interprets placeholders)
						concrete_aset = getMatchedActions(a, procsrulematches[i][j], i)
						# add this set to procsruleconcretesyncactions
						procsruleconcretesyncactions[i][j] |= concrete_aset
						for ca in concrete_aset:
							a_trans = actprocs[i].get(ca)
							if a_trans is not None:
								a_rule = actleft.get(a)
								for src, t in a_trans.items():
									found = False
									for srcm, tm in a_rule.items():
										if src in mapinfo.get(srcm):
											found = True
											break
									if not found:
										print_error("well-formedness violated! A syncing transition labelled " + str(ca) + " in process " + str(i) + " is not transformed by rule " + str(rule) + "!")
									else:
										for tgt in t:
											found = False
											for tgtm in tm:
												if tgt in mapinfo.get(tgtm):
													found = True
													break
											if not found:
												print_error("well-formedness violated! A syncing transition labelled " + str(ca) + " in process " + str(i) + " is not transformed by rule " + str(rule) + "!")

def flipMatch(mtch):
	"""produce the reverse of the given match to reason from process LTS states to rule pattern states"""
	f = {}
	for k, v in mtch[0].items():
		f[v] = k
	return f

def removeDanglingMatches(processid, rule, statemap):
	"""Remove matches that result in dangling edges"""
	global revprocs
	newstatemap = []
	for mtch in statemap:
		if mtch != [{},{}]:
			next = False 
			nr_of_deleted_states = int(((rule[0])[0])[2]) - int(((rule[0])[0])[0])
			if nr_of_deleted_states > 0:
				flipmtch = flipMatch(mtch)
				for s in range(int(((rule[0])[0])[0]), int(((rule[0])[0])[2])):
					if next:
						break
					s_process = mtch[0].get(str(s))
					outgoing = (network.procs[processid]).get(s_process)
					if outgoing is not None:
						for a, t in outgoing.items():
							if next:
								break
							for tgt in t:
								if next:
									break
								# is the tgt matched on by mtch?
								tgt_mtch = flipmtch.get(tgt)
								if tgt_mtch is None:
									next = True
									break
								else:
									out = ((rule[0])[1]).get(str(s))
									if out is None:
										next = True
										break
									else:
										outwithlabel = out.get(a)
										if outwithlabel is None:
											next = True
											break
										else:
											if tgt_mtch not in outwithlabel:
												next = True
												break
					incoming = (revprocs[processid]).get(s_process)
					if incoming is not None:
						for a, t in incoming.items():
							if next:
								break
							for src in t:
								if next:
									break
								# is the tgt matched on by mtch?
								src_mtch = flipmtch.get(src)
								if src_mtch is None:
									next = True
									break
								else:
									out = ((rule[0])[1]).get(src_mtch)
									if out is None:
										next = True
										break
									else:
										outwithlabel = out.get(a)
										if outwithlabel is None:
											next = True
											break
										else:
											if str(s) not in outwithlabel:
												next = True
												break
			if not next:
				newstatemap.append(mtch)
	return newstatemap

def removeExclusiveglueViolations(processid, rule, statemap):
	"""Remove matches that violate exclusive glue conditions"""
	global revprocs
	newstatemap = []
	for mtch in statemap:
		if mtch != [{},{}]:
			# obtain the reverse of the match to reason in the other direction
			fmtch = flipMatch(mtch)
			next = False
			if int(rule[0][0][3]) > 0:
				flipmtch = flipMatch(mtch)
				for i in range(0,int(rule[0][0][3])):
					outgoing = network.procs[processid].get(mtch[0].get(str(i)))
					if outgoing is None:
						outgoing = {}
					for a, t in outgoing.items():
						for tgt in t:
							if fmtch.get(tgt) is None:
								next = True
								break
						if next:
							break
					if next:
						break
			if not next:
				newstatemap.append(mtch)
	return newstatemap

def getAllMatches(processid, rule):
	"""get all the matches of the given rule on the given process LTS"""
	if len((rule[0])[1]) == 0:
		if rule[0][0][2] == '1':
			return [[{'0': '0'},{}]]
		else:
			return []
	else:
		return extendMatches(processid, rule, [[{},{}]])

def groupMatches(statemap):
	"""merge the info in the matches in statemap"""
	result = {}
	for mtch in statemap:
		for s, smap in mtch[0].items():
			rlt = result.get(s)
			if rlt is None:
				rlt = set([])
			rlt.add(smap)
			result[s] = rlt
	return result

def updateMatch(processid, tpl, mtch):
	"""check for a mapping of transition (k,a,tgt) on process and return all possible extensions of mtch"""
	# a match is a tuple containing:
	# 1) a mapping between states, and
	# 2) a placeholder dict
	(src,a,tgt) = tpl
	newstatemap = []
	#t = a.split(' ')
	#prefix = t[0]
	#i = 1
	#for i in range(1,len(t)):
	#	if t[i][0] != '#':
	#		prefix += ' ' + t[i]
	#	else:
	#		break
	params = action.getPlaceholder(a)
	hasplaceholder = (params != '')
	prefix = action.stripPlaceholder(a)
	if prefix[0] == '\'':
		# prefix is a regular expression
		regexpr = True
	else:
		regexpr = False
	prefixparams = ''
	if hasplaceholder:
		# is the value of the placeholder known? If so, construct the concrete action label
		if mtch[1].get(params) is not None:
			prefixparams = mtch[1].get(params)
			placeholderfound = True
		else:
			placeholderfound = False
	proc_a_trans = []
	if not regexpr and (not hasplaceholder or placeholderfound):
		# no placeholder there. We can directly fetch transitions
		proc_a_trans = (actprocs[processid]).get(prefix + prefixparams)
		if proc_a_trans is not None:
			srcmap = mtch[0].get(src)
			tgtmap = mtch[0].get(tgt)
			for src1, v in proc_a_trans.items():
				for tgt1 in v:
					addsrc = False
					addtgt = False
					if srcmap is None:
						addsrc = True
					if srcmap == src1 or addsrc:
						if tgtmap is None:
							addtgt = True
						if tgtmap == tgt1 or addtgt:
							newmtch = copy.deepcopy(mtch)
							if addsrc:
								newmtch[0][src] = src1
							if addtgt:
								newmtch[0][tgt] = tgt1
							newstatemap.append(newmtch)
	else:
		for ac, rlts in actprocs[processid].items():
			if action.isMatch(a, ac, mtch[1]):
				srcmap = mtch[0].get(src)
				tgtmap = mtch[0].get(tgt)
				for src1, v in rlts.items():
					for tgt1 in v:
						addsrc = False
						addtgt = False
						if srcmap is None:
							addsrc = True
						if srcmap == src1 or addsrc:
							if tgtmap is None:
								addtgt = True
							if tgtmap == tgt1 or addtgt:
								newmtch = copy.deepcopy(mtch)
								if addsrc:
									newmtch[0][src] = src1
								if addtgt:
									newmtch[0][tgt] = tgt1
								concrete_a = action.getPlaceholdervalue(a, ac)
								if concrete_a != "":
									newmtch[1][params] = concrete_a
								newstatemap.append(newmtch)
	return newstatemap

def extendMatchesTransition(processid, tpl, statemap):
	(src,a,tgt) = tpl
	newstatemap = []
	for mtch in statemap:
		newstatemap = newstatemap + updateMatch(processid, (src,a,tgt), mtch)
	return newstatemap

def extendMatches(processid, rule, statemap):
	skip = False
	for src, v in ((rule[0])[1]).items():
		for a, t in v.items():
			for tgt in t:
				# was +=!
				statemap = extendMatchesTransition(processid, (src,a,tgt), statemap)
				if not statemap:
					skip = True
					break
			if skip:
				break
		if skip:
			break
	return statemap

def isEmptyVector(v):
	"""is the vector v empty?"""
	for ve in v:
		if v != -1:
			return False
	return True

def constructChecks():
	"""construct the required checks for property preservation"""
	global RS, RS_vector, checks, RS_left_syncrules, RS_right_syncrules, exclsets
	tocheck = set([i for i in range(0,len(RS_vector))])
	# while we construct checks, we also construct and compare the relevant interfaces. Before and after
	# transformation, these should be the same for a given set of dependent transformation rules
	checks = []
	while tocheck != set([]):
		ri = tocheck.pop()
		c = [set([]),set([])]
		if RS_vector[ri] < len(RS):
			c[0].add(ri)
		else:
			c[1].add(ri)
		cset = {ri}
		interfaces = [Counter(), Counter()]
		eset = set([])
		next = True
		while next:
			next = False
			for side in [0,1]:
				if side == 0:
					RS_syncrules = RS_left_syncrules
				else:
					RS_syncrules = copy.deepcopy(RS_left_syncrules)
					RS_syncrules += RS_right_syncrules
				for (vects, rltact, interface) in RS_syncrules:
					add_interface = False
					for v in vects:
						# is the vector relevant?
						found = False
						for i in range(0,len(v)):
							if v[i] != '*' and i in cset:
								found = True
								break
						if found:
							for i in range(0,len(v)):
								if v[i] != '*':
									if RS_vector[i] < len(RS):
										if i not in c[0]:
											next = True
											c[0].add(i)
											cset.add(i)
									else:
										if i not in c[1]:
											next = True
											c[1].add(i)
											cset.add(i)
							add_interface = True
					if add_interface:
						# extend the left interface of the check
						for ia in set(interface.elements()):
							if interfaces[side][ia] < interface[ia]:
								interfaces[side][ia] = interface[ia]
						if len(set(interface.elements())) > 0:
							# add rltact to eset
							eset.add(rltact)
		# we have obtained a new check. Remove those rules from tocheck
		for i in range(0,len(c)):
			for ri in c[i]:
				tocheck.discard(ri)
		# compare interfaces
		if interfaces[0] != interfaces[1]:
			rset = set([])
			for ri in cset:
				rset.add(RS_vector[ri])
			print_error("inconsistency in possible synchronisation with the environment! Concerns rules " + str(rset))
		checks.append(c)
		exclsets.append(eset)

def powerset(iterable):
		"powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
		s = list(iterable)
		return itertools.chain.from_iterable(itertools.combinations(s, r) for r in range(len(s)+1))

def checkPropPresSingle(chk):
	"""Perform single property preservation check (for multi-threading)"""
	global checks, RS, RS_vector, procndivsets, systemtrans, procsrulestatemaps, revhashtable, rulematcheson, exclsets
	ccl = []
	ccr = []
	ccl_headers = []
	ccr_headers = []
	subtrset = set(chk[2])
	glue_syncvector = []
	first_gluepos = -1
	for i in range(0,len(RS_vector)):
		if i in subtrset:
			r = copy.deepcopy(RS[RS_vector[i]][0][1])
			ccl.append(r)
			r = copy.deepcopy(RS[RS_vector[i]][1][1])
			ccr.append(r)
			header = tuple(['0', RS[RS_vector[i]][0][0][1], RS[RS_vector[i]][0][0][2]])
			ccl_headers.append(header)
			header = tuple(['0', RS[RS_vector[i]][1][0][1], RS[RS_vector[i]][1][0][2]])
			ccr_headers.append(header)
			glue_syncvector.append('glue')
			if first_gluepos == -1:
				first_gluepos = i
		else:
			if i in checks[chk[1]][1]:
				# add the rules introducing new processes
				r = copy.deepcopy(RS_add[RS_vector[i]-len(RS)][0][1])
				ccl.append(r)
				r = copy.deepcopy(RS_add[RS_vector[i]-len(RS)][1][1])
				ccr.append(r)
				header = tuple(['0', RS_add[RS_vector[i]-len(RS)][0][0][1], RS_add[RS_vector[i]-len(RS)][0][0][2]])
				ccl_headers.append(header)
				header = tuple(['0', RS_add[RS_vector[i]-len(RS)][1][0][1], RS_add[RS_vector[i]-len(RS)][1][0][2]])
				ccr_headers.append(header)
				glue_syncvector.append('glue')
				if first_gluepos == -1:
					first_gluepos = i
			else:
				ccl.append({})
				ccr.append({})
				ccl_headers.append(('0','0','0'))
				ccr_headers.append(('0','0','0'))
				glue_syncvector.append('*')

# 	# extend the rule patterns by rewriting kappa-transitions
# 	for i in range(0,len(ccl)):
# 		if ccl[i] != {}:
# 			for src, v in ccl[i].items():
# 				rlt = v.get('kappa')
# 				if rlt != None:
# 					v['\"kappa_' + str(i) + "_" + src + "\""] = rlt
# 					v.pop('kappa')
# 					v1 = ccr[i].get(src)
# 					rlt = v1.get('kappa')
# 					v1['\"kappa_' + str(i) + "_" + src + "\""] = rlt
# 					v1.pop('kappa')
# 					ccr[i][src] = v1

	# add glue-rule to sync rules
	leftsync = copy.deepcopy(RS_gen_left_syncrules)
	rightsync = copy.deepcopy(RS_gen_right_syncrules)
	if first_gluepos != -1:
		leftsync[first_gluepos]['glue'] = [(glue_syncvector, 'tau')]
		rightsync[first_gluepos]['glue'] = [(glue_syncvector, 'tau')]

	# generate LTSs of networks of rule patterns
	generateLTS(ccl_headers, ccl, [], leftsync, RS_left_syncactions, os.path.join(config.rs_folder, "rleft" + str(chk[0])), opt.quiet, config.outputobject, opt.genbound, [x for x in range(0,len(ccl_headers))], 0, False, True, False)
	generateLTS(ccr_headers, ccr, [], rightsync, RS_right_syncactions, os.path.join(config.rs_folder, "rright" + str(chk[0])), opt.quiet, config.outputobject, opt.genbound, [x for x in range(0,len(ccr_headers))], 0, False, True, False)

	if opt.divergency:
		# 1. CHECK THAT NO DIVERGENCY IS LOST ON GLUE-STATES WHEN refining
		# ONLY NEEDED WHEN OPT.DIVERGENCY IS TRUE, OTHERWISE THIS IS PART
		# OF THE BISIM CHECK AUTOMATICALLY
		#print_message("checking for divergency preservation")
		[local_header, local_trans, local_actset] = aut.read(config.rs_folder, "rleft" + str(chk[0]) + ".aut")
		local_map = readMap(config.rs_folder, "rleft" + str(chk[0]))
		# determine set of diverging states
		divset = computeDivergencySet(local_header, local_trans)
		# construct the set of state vectors that consist only of glue-states
		ldivvectors = set([])
		for s in divset:
			svec = local_map.get(s)
			mustadd = True
			for i in range(0,len(ccl)):
				if ccl[i] != {}:
					if int(s[i]) >= ccl_headers[i][0]:
						mustadd = False
			if mustadd:
				ldivvectors.add(tuple(svec))
		[local_header, local_trans, local_actset] = aut.read(config.rs_folder, "rright" + str(chk[0]) + ".aut")
		local_map = readMap(config.rs_folder, "rright" + str(chk[0]))
		# determine set of diverging states
		divset = computeDivergencySet(local_header, local_trans)
		# construct the set of state vectors
		rdivvectors = set([])
		for s in divset:
			svec = local_map.get(s)
			rdivvectors.add(tuple(svec))
		# compare the divvector sets
		if not ldivvectors <= rdivvectors:
			print_error("Transformation may remove diverging behaviour!")
		# 2. ADD DIVERGENCY INFO TO RULE NETWORKS AND COMPARE
		# add tau-selfloops to diverging states in left and right patterns
		for i in range(0,len(ccl)):
			if ccl[i] != {}:
				# We have to skip the source state if we previously added a new initial state)
				skip_src = False
				if int(RS[RS_vector[i]][0][0][0]) > 1:
					skip_src = True
				for src, v in ccl[i].items():
					if skip_src:
						srcmin = str(int(src)-1)
					else:
						srcmin = src
					if int(srcmin) > -1:
						addtau = True
						for pid in rulematcheson[RS_vector[i]]:
							mapset = procsrulestatemaps[pid][RS_vector[i]].get(srcmin)
							if mapset is None:
								mapset = set([])
							if mapset & procndivsets[i] != set([]):
								addtau = False
								break
						if addtau:
							rlt = v.get('tau')
							if rlt is None:
								rlt = set([])
							if src not in rlt:
								rlt.add(src)
								ccl_headers[i] = (ccl_headers[i][0], str(int(ccl_headers[i][1])+1), ccl_headers[i][2])
								v['tau'] = rlt
							# if src is a glue-state, also add this tau-loop to the right network
							if int(srcmin) < int(RS[RS_vector[i]][0][0][0]):
								vr = ccr[i].get(src)
								rlt = vr.get('tau')
								if rlt is None:
									rlt = set([])
								if src not in rlt:
									rlt.add(src)
									ccr_headers[i] = (ccr_headers[i][0], str(int(ccr_headers[i][1])+1), ccr_headers[i][2])
									vr['tau'] = rlt
									ccr[i][src] = vr
		# generate LTSs of networks of rule patterns, now with divergency information
		generateLTS(ccl_headers, ccl, [], leftsync, RS_left_syncactions, os.path.join(config.rs_folder, "rleft" + str(chk[0])), opt.quiet, config.outputobject, opt.genbound, [x for x in range(0,len(ccl_headers))], set([]), False, False, True, False)
		generateLTS(ccr_headers, ccr, [], rightsync, RS_right_syncactions, os.path.join(config.rs_folder, "rright" + str(chk[0])), opt.quiet, config.outputobject, opt.genbound, [x for x in range(0,len(ccr_headers))], set([]), False, False, True, False)

	# hide the necessary actions
	try:
		inFile = open(os.path.join(config.rs_folder, "rleft" + str(chk[0]) + ".aut"),'r')
	except IOError:
		exit(1)
	hideActions(config.rs_folder, "rleft" + str(chk[0]), exclsets[chk[1]], "")
	try:
		inFile = open(os.path.join(config.rs_folder, "rright" + str(chk[0]) + ".aut"),'r')
	except IOError:
		exit(1)
	hideActions(config.rs_folder, "rright" + str(chk[0]), exclsets[chk[1]], "")

	# perform bisim check
	if opt.fairness:
		#print_message("checking branching bisimilarity of left and right rule network LTSs")
		#rlt = subprocess.check_call(["ltscompare", "--equivalence=branching-bisim", os.path.join(network.folder, "rleft" + str(chk[0]) + "_hidden.aut"), os.path.join(network.folder, "rright" + str(chk[0]) + "_hidden.aut")], stderr=subprocess.PIPE)
		rlt = subprocess.Popen(["ltscompare", "--equivalence=branching-bisim", os.path.join(config.rs_folder, "rleft" + str(chk[0]) + "_hidden.aut"), os.path.join(config.rs_folder, "rright" + str(chk[0]) + "_hidden.aut")], stderr=subprocess.PIPE)
	else:
		#print_message("checking divergence-sensitive branching bisimilarity of left and right rule network LTSs")
		rlt = subprocess.Popen(["ltscompare", "--equivalence=dpbranching-bisim", os.path.join(config.rs_folder, "rleft" + str(chk[0]) + "_hidden.aut"), os.path.join(config.rs_folder, "rright" + str(chk[0]) + "_hidden.aut")], stderr=subprocess.PIPE)

	out, err = rlt.communicate()
	#print(out)
	#print(err)
	i = str(err).find('not')
	if i == -1:
		# clean up temporary files
		return 0
	#	if opt.fairness:
			#print_message("LTSs are branching bisimilar")
	#	else:
			#print_message("LTSs are divergence-sensitive branching bisimilar")
	else:
		return chk[0]
		#if opt.fairness:
			#print_message("check " + str(checknr) + ": LTSs are not branching bisimilar")
		#else:
			#print_message("check " + str(checknr) + ": LTSs are not divergence-sensitive branching bisimilar")

def extendRule(rid):
	"""Extend the given rule for property preservation checking"""
	global RS, RS_vector
	# add a new kappa state connected to all glue-states in the rule patterns via kappa-transitions.
	# all glue-states have an incoming kappa-transition from this state, and all non-exclusive glue-states
	# have an outgoing kappa-transition to this state.
	# Besides the kappa-state, a new initial state is added, which has outgoing `glue'-transitions to both the kappa-state
	# and all the glue-states.

	# rule header format:
	# 0: number of glue-states
	# 1: number of transitions
	# 2: number of states
	# 3: number of exclusive glue-states
	for i in [0,1]:
		if RS_vector[rid] < len(RS):
			rule = RS[RS_vector[rid]]
		else:
			rule = RS_add[RS_vector[rid]-len(RS)]
		ntrans = int(rule[i][0][1])
		newr = {}
		for j in range(0,int(rule[i][0][2])):
			v = rule[i][1].get(str(j),{})
			newv = {}
			for a, t in v.items():
				newv[a] = set([str(int(x)+2) for x in t])
			# add outgoing kappa-transition?
			if j < int(rule[i][0][0]) and (j >= int(rule[i][0][3]) or int(rule[i][0][3]) == 0):
				newv['kappa_' + str(rid) + "_" + str(j+2) + "_1"] = {'1'}
				ntrans += 1
			newr[str(j+2)] = newv
		# add new kappa-state, with kappa transitions to the glue-states
		outk = {}
		for x in range(2,int(rule[i][0][0])+2):
			outk['kappa_' + str(rid) + "_1_" + str(x)] = {str(x)}
		newr['1'] = outk
		#newr['1'] = {'kappa': set([str(x) for x in range(2,int(rule[i][0][0])+2)])}
		ntrans += int(rule[i][0][0])
		# add new initial state, with 'glue'-transitions to the kappa-state and the glue-states
		newr['0'] = {'glue': {'1'} | set([str(x) for x in range(int(rule[i][0][3])+2,int(rule[i][0][0])+2)])}
		ntrans += 1+int(rule[i][0][0])-int(rule[i][0][3])
		rule[i][1] = newr
		rule[i][0] = (rule[i][0][0], str(ntrans), str(int(rule[i][0][2])+2), rule[i][0][3])

def checkPropPreservationNew():
	"""New version of procedure to check property preservation of RS"""
	global checks, RS, RS_vector, procndivsets, systemtrans, procsrulestatemaps, revhashtable, RS_gen_left_syncrules, RS_gen_right_syncrules, RS_left_syncactions, RS_right_syncactions
	checks_done = set([])

	for i in RS_vector:
		extendRule(i)
	# add a sync rule for 'glue'-transitions
# 	newsrule = (['glue' for i in range(0,len(RS_vector))], 'tau')
# 	RS_gen_left_syncrules[0]['glue'] = [newsrule]
# 	RS_gen_right_syncrules[0]['glue'] = [newsrule]
	# register 'glue' as a sync action
	for i in RS_vector:
		RS_left_syncactions[i].add('glue')
		RS_right_syncactions[i].add('glue')
	
	# ADD RULES DO NOT NEED EXTENSIONS!
	#for rule in RS_add:
	#	extendRule(rule)
	# perform the checks
	nrofchecks = 0
	checknr = 0
	# list of actual checks to perform
	bisim_checks = []
	for ci in range(0,len(checks)):
		# consider any subset of transformation rules
		pp = tuple(checks[ci][0])
		checknr += 1
		bisim_checks.append((checknr, ci, pp))
		nrofchecks += 1
	pool = multiprocessing.Pool(min(multiprocessing.cpu_count(), config.nrthreads))
	counterexamples = []
	r = pool.map_async(checkPropPresSingle, bisim_checks, callback=counterexamples.append)
	r.wait()
	#res = checkPropPresSingle(bisim_checks[0])
	#counterexamples.append([res])
	# if relevant, construct counter-example
	error = False
	#print(counterexamples)
	for ce in counterexamples[0]:
		if ce == -1:
			print_error("Transformation may remove divergent behaviour!")
		else:
			if ce > 0:
				if opt.divergency:
					print_message("PROPERTY NOT PRESERVED: preservation of " + config.property_name + " for network " + network.name + " violated!")
				else:
					if config.property_name != "":
						print_message("PROPERTY NOT PRESERVED: preservation of " + config.property_name + " violated!")
					else:
						print_message("SEMANTICS NOT PRESERVED: semantics preservation violated!")
				print_message('---')
				if not opt.divergency:
					print_message("try to run the check again with the 'fairness' option, or do a model-dependent check")
				print_message("relevant rule networks and LTSs are written to disk as rleft.1.(exp/aut) and rright.1.(exp/aut)")
				os.rename(os.path.join(config.rs_folder, "rleft" + str(ce) + ".aut"), os.path.join(config.rs_folder, "rleft.1.aut"))
				os.rename(os.path.join(config.rs_folder, "rright" + str(ce) + ".aut"), os.path.join(config.rs_folder, "rright.1.aut"))
				os.rename(os.path.join(config.rs_folder, "rleft" + str(ce) + "_hidden.aut"), os.path.join(config.rs_folder, "rleft_hidden.1.aut"))
				os.rename(os.path.join(config.rs_folder, "rright" + str(ce) + "_hidden.aut"), os.path.join(config.rs_folder, "rright_hidden.1.aut"))
				# write the two rule networks to disk
				for i in range(0,len(bisim_checks)):
					if bisim_checks[i][0] == ce:
						ci_ce_ad = checks[bisim_checks[i][1]][1]
						pp_ce = bisim_checks[i][2]
						break
				ccl = []
				ccr = []
				ccl_headers = []
				ccr_headers = []
				for i in range(0,len(RS_vector)):
					if i in pp_ce:
						r = copy.deepcopy(RS[RS_vector[i]][0][1])
						ccl.append(r)
						r = copy.deepcopy(RS[RS_vector[i]][1][1])
						ccr.append(r)
						header = tuple(['0', RS[RS_vector[i]][0][0][1], RS[RS_vector[i]][0][0][2]])
						ccl_headers.append(header)
						header = tuple(['0', RS[RS_vector[i]][1][0][1], RS[RS_vector[i]][1][0][2]])
						ccr_headers.append(header)
					else:
						if i in ci_ce_ad:
							r = copy.deepcopy(RS_add[RS_vector[i]-len(RS)][0][1])
							ccl.append(r)
							r = copy.deepcopy(RS_add[RS_vector[i]-len(RS)][1][1])
							ccr.append(r)
							header = tuple(['0', RS_add[RS_vector[i]-len(RS)][0][0][1], RS_add[RS_vector[i]-len(RS)][0][0][2]])
							ccl_headers.append(header)
							header = tuple(['0', RS_add[RS_vector[i]-len(RS)][1][0][1], RS_add[RS_vector[i]-len(RS)][1][0][2]])
							ccr_headers.append(header)
						else:
							ccl.append({})
							ccr.append({})
							ccl_headers.append(('0','0','0'))
							ccr_headers.append(('0','0','0'))
				# extend the rule patterns by rewriting kappa-selfloops
				for i in range(0,len(ccl)):
					if ccl[i] != {}:
						for src, v in ccl[i].items():
							rlt = v.get('kappa')
							if rlt is not None:
								v['\"kappa_' + str(i) + "_" + src + "\""] = rlt
								v.pop('kappa')
								v1 = ccr[i].get(src)
								rlt = v1.get('kappa')
								v1['\"kappa_' + str(i) + "_" + src + "\""] = rlt
								v1.pop('kappa')
								ccr[i][src] = v1
				rfiles = []
				for i in range(0,len(ccl)):
					if ccl[i] == {}:
						rfiles.append('empty.aut')
					else:
						rfiles.append('rlpat_' + str(i) + '.aut')
				network.write(config.rs_folder, ccl, ccl_headers, rfiles, RS_gen_left_syncrules, "rleft")
				for i in range(0,len(ccl)):
					if rfiles[i] != 'empty.aut' or ccr[i] != {}:
						rfiles[i] = 'rrpat_' + str(i) + '.aut'					
				network.write(config.rs_folder, ccr, ccr_headers, rfiles, RS_gen_right_syncrules, "rright")
				error = True
				break
	# done
	if not error:
		#print_message('---')
		if opt.divergency:
			print_message("PROPERTY PRESERVED: preservation of " + config.property_name + " for network " + network.name + " determined after " + str(nrofchecks) + " checks")
		else:
			if opt.fairness:
				print_message("PROPERTY PRESERVED UNDER FAIRNESS: preservation of " + config.property_name + " determined after " + str(nrofchecks) + " checks")
			elif config.property_name != "":
				print_message("PROPERTY PRESERVED: preservation of " + config.property_name + " determined after " + str(nrofchecks) + " checks")
			else:
				print_message("SEMANTICS PRESERVED: semantics preservation determined after " + str(nrofchecks) + " checks")
		print_message('---')
	#clean up temporary files
	for i in range(1,len(bisim_checks)+1):
		if os.path.isfile(os.path.join(config.rs_folder, "rleft" + str(i) + ".aut")):
			os.remove(os.path.join(config.rs_folder, "rleft" + str(i) + ".aut"))
		if os.path.isfile(os.path.join(config.rs_folder, "rright" + str(i) + ".aut")):
			os.remove(os.path.join(config.rs_folder, "rright" + str(i) + ".aut"))
		if os.path.isfile(os.path.join(config.rs_folder, "rleft" + str(i) + ".map")):
			os.remove(os.path.join(config.rs_folder, "rleft" + str(i) + ".map"))
		if os.path.isfile(os.path.join(config.rs_folder, "rright" + str(i) + ".map")):
			os.remove(os.path.join(config.rs_folder, "rright" + str(i) + ".map"))
		if os.path.isfile(os.path.join(config.rs_folder, "rleft" + str(i) + "_hidden.aut")):
			os.remove(os.path.join(config.rs_folder, "rleft" + str(i) + "_hidden.aut"))
		if os.path.isfile(os.path.join(config.rs_folder, "rright" + str(i) + "_hidden.aut")):
			os.remove(os.path.join(config.rs_folder, "rright" + str(i) + "_hidden.aut"))
		if os.path.isfile(os.path.join(config.rs_folder, "rleft" + str(i) + "_hidden.map")):
			os.remove(os.path.join(config.rs_folder, "rleft" + str(i) + "_hidden.map"))
		if os.path.isfile(os.path.join(config.rs_folder, "rright" + str(i) + "_hidden.map")):
			os.remove(os.path.join(config.rs_folder, "rright" + str(i) + "_hidden.map"))	

def	checkPropPreservation():
	"""Check property preservation of RS"""
	#NEW CHECK: ALSO ADD DIVERGENCY LOOPS IN RIGHT PATTERNS, CHECK FOR DIV PRESERVATION BY CHECKING
	#DIVERGENCY SETS LEFT AND RIGHT, AND THAT RIGHT IS SUPERSET OF LEFT
	global checks, RS, RS_vector, procndivsets, systemtrans, procsrulestatemaps, revhashtable
	checks_done = set([])

	for i in RS_vector:
		extendRule(i)
	# add a sync rule for 'glue'-transitions
# 	newsrule = (['glue' for i in range(0,len(RS_vector))], 'tau')
# 	RS_gen_left_syncrules[0]['glue'] = [newsrule]
# 	RS_gen_right_syncrules[0]['glue'] = [newsrule]
	# register 'glue' as a sync action
	for i in RS_vector:
		RS_left_syncactions[i].add('glue')
		RS_right_syncactions[i].add('glue')

	# ADD RULES DO NOT NEED EXTENSIONS!
	#for rule in RS_add:
	#	extendRule(rule)
	# perform the checks
	nrofchecks = 0
	checknr = 0
	# list of actual checks to perform
	bisim_checks = []
	for ci in range(0,len(checks)):
		# consider any subset of transformation rules
		for pp in powerset(checks[ci][0]):
			# obtain the check configurations
			# skip the empty config
			if len(pp) > 0:
				checksig = tuple([RS_vector[i] for i in pp])
				if checksig not in checks_done:
					checknr += 1
					bisim_checks.append((checknr, ci, pp))
					checks_done.add(checksig)
					nrofchecks += 1
	pool = multiprocessing.Pool(min(multiprocessing.cpu_count(), config.nrthreads))
	counterexamples = []
	r = pool.map_async(checkPropPresSingle, bisim_checks, callback=counterexamples.append)
	r.wait()
	#res = checkPropPresSingle(bisim_checks[0])
	#counterexamples.append([res])
	# if relevant, construct counter-example
	error = False
	for ce in counterexamples[0]:
		if ce == -1:
			print_error("Transformation may remove divergent behaviour!")
		else:
			if ce > 0:
				if opt.divergency:
					print_message("PROPERTY NOT PRESERVED: preservation of " + config.property_name + " for network " + network.name + " violated!")
				else:
					if config.property_name != "":
						print_message("PROPERTY NOT PRESERVED: preservation of " + config.property_name + " violated!")
					else:
						print_message("SEMANTICS NOT PRESERVED: semantics preservation violated!")
				print_message('---')
				if not opt.divergency:
					print_message("try to run the check again with the 'fairness' option, or do a model-dependent check")
				print_message("relevant rule networks and LTSs are written to disk as rleft.1.(exp/aut) and rright.1.(exp/aut)")
				os.rename(os.path.join(config.rs_folder, "rleft" + str(ce) + ".aut"), os.path.join(config.rs_folder, "rleft.1.aut"))
				os.rename(os.path.join(config.rs_folder, "rright" + str(ce) + ".aut"), os.path.join(config.rs_folder, "rright.1.aut"))
				os.rename(os.path.join(config.rs_folder, "rleft" + str(ce) + "_hidden.aut"), os.path.join(config.rs_folder, "rleft_hidden.1.aut"))
				os.rename(os.path.join(config.rs_folder, "rright" + str(ce) + "_hidden.aut"), os.path.join(config.rs_folder, "rright_hidden.1.aut"))
				# write the two rule networks to disk
				for i in range(0,len(bisim_checks)):
					if bisim_checks[i][0] == ce:
						ci_ce_ad = checks[bisim_checks[i][1]][1]
						pp_ce = bisim_checks[i][2]
						break
				ccl = []
				ccr = []
				ccl_headers = []
				ccr_headers = []
				for i in range(0,len(RS_vector)):
					if i in pp_ce:
						r = copy.deepcopy(RS[RS_vector[i]][0][1])
						ccl.append(r)
						r = copy.deepcopy(RS[RS_vector[i]][1][1])
						ccr.append(r)
						header = tuple(['0', RS[RS_vector[i]][0][0][1], RS[RS_vector[i]][0][0][2]])
						ccl_headers.append(header)
						header = tuple(['0', RS[RS_vector[i]][1][0][1], RS[RS_vector[i]][1][0][2]])
						ccr_headers.append(header)
					else:
						if i in ci_ce_ad:
							r = copy.deepcopy(RS_add[RS_vector[i]-len(RS)][0][1])
							ccl.append(r)
							r = copy.deepcopy(RS_add[RS_vector[i]-len(RS)][1][1])
							ccr.append(r)
							header = tuple(['0', RS_add[RS_vector[i]-len(RS)][0][0][1], RS_add[RS_vector[i]-len(RS)][0][0][2]])
							ccl_headers.append(header)
							header = tuple(['0', RS_add[RS_vector[i]-len(RS)][1][0][1], RS_add[RS_vector[i]-len(RS)][1][0][2]])
							ccr_headers.append(header)
						else:
							ccl.append({})
							ccr.append({})
							ccl_headers.append(('0','0','0'))
							ccr_headers.append(('0','0','0'))
				# extend the rule patterns by rewriting kappa-selfloops
				for i in range(0,len(ccl)):
					if ccl[i] != {}:
						for src, v in ccl[i].items():
							rlt = v.get('kappa')
							if rlt is not None:
								v['\"kappa_' + str(i) + "_" + src + "\""] = rlt
								v.pop('kappa')
								v1 = ccr[i].get(src)
								rlt = v1.get('kappa')
								v1['\"kappa_' + str(i) + "_" + src + "\""] = rlt
								v1.pop('kappa')
								ccr[i][src] = v1
				rfiles = []
				for i in range(0,len(ccl)):
					if ccl[i] == {}:
						rfiles.append('empty.aut')
					else:
						rfiles.append('rlpat_' + str(i) + '.aut')
				network.write(config.rs_folder, ccl, ccl_headers, rfiles, RS_gen_left_syncrules, "rleft")
				for i in range(0,len(ccl)):
					if rfiles[i] != 'empty.aut' or ccr[i] != {}:
						rfiles[i] = 'rrpat_' + str(i) + '.aut'					
				network.write(config.rs_folder, ccr, ccr_headers, rfiles, RS_gen_right_syncrules, "rright")
				error = True
				break
	# done
	if not error:
		#print_message('---')
		if opt.divergency:
			print_message("PROPERTY PRESERVED: preservation of " + config.property_name + " for network " + network.name + " determined after " + str(nrofchecks) + " checks")
		else:
			if opt.fairness:
				print_message("PROPERTY PRESERVED UNDER FAIRNESS: preservation of " + config.property_name + " determined after " + str(nrofchecks) + " checks")
			elif config.property_name != "":
				print_message("PROPERTY PRESERVED: preservation of " + config.property_name + " determined after " + str(nrofchecks) + " checks")
			else:
				print_message("SEMANTICS PRESERVED: semantics preservation determined after " + str(nrofchecks) + " checks")
		print_message('---')
	#clean up temporary files
	for i in range(1,len(bisim_checks)+1):
		if os.path.isfile(os.path.join(config.rs_folder, "rleft" + str(i) + ".aut")):
			os.remove(os.path.join(config.rs_folder, "rleft" + str(i) + ".aut"))
		if os.path.isfile(os.path.join(config.rs_folder, "rright" + str(i) + ".aut")):
			os.remove(os.path.join(config.rs_folder, "rright" + str(i) + ".aut"))
		if os.path.isfile(os.path.join(config.rs_folder, "rleft" + str(i) + ".map")):
			os.remove(os.path.join(config.rs_folder, "rleft" + str(i) + ".map"))
		if os.path.isfile(os.path.join(config.rs_folder, "rright" + str(i) + ".map")):
			os.remove(os.path.join(config.rs_folder, "rright" + str(i) + ".map"))
		if os.path.isfile(os.path.join(config.rs_folder, "rleft" + str(i) + "_hidden.aut")):
			os.remove(os.path.join(config.rs_folder, "rleft" + str(i) + "_hidden.aut"))
		if os.path.isfile(os.path.join(config.rs_folder, "rright" + str(i) + "_hidden.aut")):
			os.remove(os.path.join(config.rs_folder, "rright" + str(i) + "_hidden.aut"))
		if os.path.isfile(os.path.join(config.rs_folder, "rleft" + str(i) + "_hidden.map")):
			os.remove(os.path.join(config.rs_folder, "rleft" + str(i) + "_hidden.map"))
		if os.path.isfile(os.path.join(config.rs_folder, "rright" + str(i) + "_hidden.map")):
			os.remove(os.path.join(config.rs_folder, "rright" + str(i) + "_hidden.map"))

# END functions for transformation rules / performing transformations on a network

def isIn(a, actions, startindex):
	"""Check if a is a superstring of an element in actions from startindex. If a contains '*' characters, do a more thorough scan"""
	for i in range(startindex,len(actions)):
		# two types actions: 1) strings enclosed by ", 2) regexps enclosed by '
		if actions[i][0] == '\'':
			exp = actions[i][1:][:-1]
			p = re.compile('"' + exp + '"')
			if p.match(a) is not None:
				return True
		else:
			if actions[i] in a:
				return True
	return False

def writeHideActions():
	"""Write the hide actions to opt.constructhidingset.hs"""
	global hideactions
	outfile = open(os.path.join(config.property_folder, config.property_name + ".hs"), 'w')
	first = True
	firstact = True
	for i in range(0,len(hideactions)):
		if hideactions[i] == 'none':
			outfile.write(hideactions[i])
			outfile.close()
			return
		if hideactions[i] == 'all' or hideactions[i] == 'but':
			if not first:
				outfile.write(' ')
			else:
				first = False
			outfile.write(hideactions[i])
		else:
			if not firstact:
				outfile.write(', ')
			else:
				outfile.write(' ')
				firstact = False
			outfile.write(hideactions[i])
	outfile.close()

def readHideActions(hideFile):
	"""Read an action hide file"""
	global hideactions
	lines = hideFile.readlines()
	line = ""
	for l in lines:
		line += l.rstrip()
	tmp = line.split()
	hideactions = []
	hasall = False
	hasbut = False
	if tmp[0] == 'none':
		hideactions.append(tmp[0])
		return
	if tmp[0] == 'all':
		hideactions.append(tmp[0])
		hasall = True
	if len(tmp) > 1:
		if tmp[1] == 'but':
			hideactions.append(tmp[1])
			hasbut = True
		if len(tmp) > 2:
			if hasbut:
				line = line[8:]
			elif hasall:
				line = line[4:]
			tmp = (line.rstrip()).split(', ')
			for x in tmp:
				#if x[0] == '"' or x[0] == '\'':
				#	x = x[1:][:-1]
				hideactions.append(x)

def hideAction(a, exclset):
	"""Hide action a according to hideactions. Actions in exclset should not be hidden"""
	global hiddenactions, hideactions
	if a.find('kappa') != -1:
		return a
	a_prefix = action.stripParams(a)
	if a_prefix in exclset:
		return a
	if not hideactions:
		return a
	if hideactions[0] == 'none':
		return a
	if a == 'i' or a == 'tau':
		return 'tau'
	if len(hideactions) == 1 and hideactions[0]=='all':
		return 'tau'
	elif len(hideactions) > 1 and hideactions[0]=='all' and hideactions[1]=='but':
		if len(hideactions) == 2:
			return 'tau'
		elif a in hiddenactions:
			return a
		elif isIn(a, hideactions, 2):
			hiddenactions.add(a)
			return a
		else:
			return 'tau'
	elif a in hiddenactions:
		return 'tau'
	elif isIn(a, hideactions, 0):
		hiddenactions.add(a)
		return 'tau'
	else:
		return a

def hideActions(folder, autbase, exclset, outputfiletail):
	"""Hide the actions in hideactions in the given .aut file, and write the result. Actions in exclset should not be hidden"""
	global hiddenactions

	if os.path.isfile(os.path.join(folder, autbase + "_hidden" + outputfiletail + ".aut")):
		os.remove(os.path.join(folder, autbase + "_hidden" + outputfiletail + ".aut"))

	# output file
	outFile = open(os.path.join(folder, autbase + "_hidden" + outputfiletail + ".aut"), 'w')
	# reset hiddenactions
	hiddenactions = set([])
	
	first = True
	for transline in open(os.path.join(folder, autbase + ".aut")):
		if first:
			# first copy header
			outFile.write(transline)
			first = False
		else:
# 			tl, remainder = aut.scanner.scan(transline)
# 			src = str(tl[0][1])
# 			act = str(tl[1][1])
# 			tgt = str(tl[2][1])
			transsplit = transline.split('"')
			src = transsplit[0].split(',')
			src = src[0][1:]
			act = transsplit[1]
			tgt = transsplit[2].split(',')
			tgt = tgt[1]
			if tgt[0] == ' ':
				tgt = tgt[1:]
			tgt = tgt.split(')')
			tgt = tgt[0]
			# remove quotes
			act = act.replace('\'', '')
			act = act.replace('"', '')
			# remove spaces
			act = act.replace(' ', '')
			outFile.write('(' + src + ', "' + hideAction(act, exclset) + '", ' + tgt + ')\n')
	outFile.close()

# def hideActionsinDict():
# 	"""hide the actions in systemtrans according to the hideactions list"""
# 	global systemtrans
# 	hiddentrans = {}
# 	for src, v in systemtrans.items():
# 		hiddentrans[src] = {}
# 		outtau = v.get('"tau"')
# 		if outtau == None:
# 			outtau = set([])
# 		for a, t in v.items():
# 			if hideAction(a) == '"tau"':
# 				outtau = outtau | t
# 			else:
# 				(hiddentrans[src])[a] = t
# 		if outtau != set([]):
# 			(hiddentrans[src])['"tau"'] = outtau
# 	systemtrans = hiddentrans

def mustSync(action, i, syncactions):
	"""Must the action sync in process i?"""
#	for ac in syncactions[i]:
#		if action.isMatch(action, ac):
#			return True
#	return False
	action_stripped = action.stripParams(action)
	return action_stripped in syncactions[i]

def peek(stack):
	"""Return but do not pop top element of stack"""
	return stack[len(stack)-1]

def setdiv(stack):
	"""Set divergency flag of top element on stack to true"""
	(stack[len(stack)-1])[2] = True

def computeDivergencySet(header, trans):
	"""Compute the set of tau-diverging states in the (hidden) system LTS that are in the given set of states"""
	# the resulting set of diverging states
	divset = set([])

	# DFS stack
	stack = []
	stackset = set([])
	# visited set
	V = set([])
	# iterate over all states
	for i in range(0,int(header[2])):
		s = str(i)
		# current divergency status on path in stack
		divreach = False
		if s not in V:
			targets = set([])
			outgoing = trans.get(s)
			if outgoing is not None:
				for a, v in outgoing.items():
					if hideAction(a, set([])) == 'tau':
						targets = targets | v
			stack.append([s,targets,False])
			stackset.add(s)

		while len(stack) > 0:
			[s,targets,isdiv] = peek(stack)
			# are there targets left to explore?
			nextfound = False
			while (not nextfound) and len(targets) > 0:
				next = targets.pop()
				if next in stackset:
					# tau-cycle found
					isdiv = True
				else:
					if next not in V:
						nextfound = True
					else:
						if next in divset:
							isdiv = True
			divreach = divreach or isdiv
			if len(targets) == 0 and not nextfound:
				if divreach:
					divset.add(s)
				V.add(s)
				stack.pop()
				stackset.remove(s)
			else:
				if divreach:
					setdiv(stack)
				divreach = False
				targets = set([])
				outgoing = trans.get(next)
				if outgoing is not None:
					for a, v in outgoing.items():
						if hideAction(a, set([])) == 'tau':
							targets = targets | v
				stack.append([next,targets,False])
				stackset.add(next)
	return divset

def computeNonDivergingProcessStates():
	"""Compute the non-diverging process states"""
	# fill the sets of non tau-diverging process states
	global revhashtable, procndivsets, divergencyset
	hel = revhashtable['0']
	#!
	for i in range(0,len(hel)):
		procndivsets.append(set([]))
	for i in range(0,int(systemLTSheader[2])):
		if str(i) not in divergencyset:
			hel = revhashtable.get(str(i))
			for j in range(0,len(hel)):
				(procndivsets[j]).add(hel[j])

def updateNonDivergingProcessStates():
	"""Update the sets of non-diverging states after a transformation"""
	# Pre-condition: the RS is property preserving
	global transformed_procs_new_states, checks, newsyncrules, RS, RS_vector, procndivsets, systemtrans, divergencyset, revhashtable, procsrulestatemaps, systemLTSheader, hashtable
	RS_nrgluestates = []
	rulendivsets = []
	for i in range(0,len(transformed_procs_new_states)):
		newl = []
		for j in range(0,len(RS)):
			newl.append(set([]))
		for j in range(0,len(RS_add)):
			newl.append(set([]))
		rulendivsets.append(newl)
	# add a new root state connected to all glue-states in the right rule patterns via tau-transitions
	for i in [0,1]:
		if i == 0:
			RS_rules = RS
		else:
			RS_rules = RS_add
		for rule in RS_rules:
			if int(rule[1][0][0]) > 1:
				ntrans = int(rule[1][0][1])
				newr = {}
				for j in range(0,int(rule[1][0][2])):
					v = rule[1][1].get(str(j))
					newv = {}
					if v is not None:
						for a, t in v.items():
							newv[a] = set([str(int(x)+1) for x in t])
					newr[str(j+1)] = newv
				newr['0'] = {'tau': set([str(x) for x in range(1,int(rule[1][0][0])+1)])}
				ntrans += int(rule[1][0][0])
				rule[1][1] = newr
				RS_nrgluestates.append(rule[1][0][0])
				rule[1][0] = ('0', str(ntrans), str(int(rule[1][0][2])+1), rule[1][0][3])
			else:
				RS_nrgluestates.append(rule[1][0][0])
				rule[1][0] = ('0', rule[1][0][1], rule[1][0][2], rule[1][0][3])
	# for each check, compute the rule network LTSs, and update the new ndiv sets based on divergency checks in those LTSs
	for ci in range(0,len(checks)):
		# consider any subset of transformation rules
		for pp in powerset(checks[ci][0]):
			# obtain the check configurations
			# skip the empty config
			if len(pp) > 0:
				ccr = []
				ccr_headers = []
				for i in range(0,len(RS_vector)):
					if i in pp:
						r = copy.deepcopy(RS[RS_vector[i]][1][1])
						ccr.append(r)
						header = tuple(['0', RS[RS_vector[i]][1][0][1], RS[RS_vector[i]][1][0][2]])
						ccr_headers.append(header)
					else:
						if i in checks[ci][1]:
							# add the rules introducing new processes
							r = copy.deepcopy(RS_add[RS_vector[i]-len(RS)][1][1])
							ccr.append(r)
							header = tuple(['0', RS_add[RS_vector[i]-len(RS)][1][0][1], RS_add[RS_vector[i]-len(RS)][1][0][2]])
							ccr_headers.append(header)
						else:
							ccr.append({})
							ccr_headers.append(('0','0','0'))
				# extend the rule patterns by adding tau-selfloops to diverging states in right patterns
				for i in range(0,len(ccr)):
					if ccr[i] != {}:
						for src in range(0,int(RS_nrgluestates[RS_vector[i]])):
							src = str(src)
							addtau = True
							for pid in rulematcheson[RS_vector[i]]:
								mapset = procsrulestatemaps[pid][RS_vector[i]].get(src)
								if mapset is None:
									mapset = set([])
								if mapset & procndivsets[i] != set([]):
									addtau = False
									break
							if addtau:
								v = ccr[i].get(src)
								rlt = v.get('tau')
								if rlt is None:
									rlt = set([])
								if src not in rlt:
									rlt.add(src)
									ccr_headers[i] = (ccr_headers[i][0], str(int(ccr_headers[i][1])+1), ccr_headers[i][2])
									v['tau'] = rlt
				# generate right rule network LTS
				generateLTS(ccr_headers, ccr, [], RS_gen_right_syncrules, RS_right_syncactions, os.path.join(config.rs_folder, "rright"), opt.quiet, config.outputobject, opt.genbound, list(range(0,len(ccr_headers))), 0, False, True, False)
				[systemLTSheader, systemtrans, systemactset] = aut.read(config.rs_folder, "rright.aut")
				revhashtable = readMap(config.rs_folder, "rright")
				# compute divergency set for this network
				divergencyset = computeDivergencySet(systemLTSheader, systemtrans)
				for i in range(0,int(systemLTSheader[2])):
					if str(i) not in divergencyset:
						# obtain the state vector
						sv = revhashtable.get(str(i))
						# for each element in the vector, add it to the corresponding rulendivset of the matching procs
						for j in range(0,len(RS_vector)):
							if j in pp or j in checks[ci][1]:
								for pid in rulematcheson[RS_vector[j]]:
									rulendivsets[pid][RS_vector[j]].add(sv[j])
	# All states in rulendivsets relate to new non-diverging states in the process
	for i in range(0,len(transformed_procs_new_states)):
		newndivstates = set([])
		length = len(RS) + len(RS_add)
		for j in range(0,length):
			for s in rulendivsets[i][j]:
				tmp = transformed_procs_new_states[i][j].get(s)
				if tmp is None:
					tmp = set([])
				newndivstates = newndivstates | tmp
		procndivsets[i] = procndivsets[i] | newndivstates

# --- functions for compositional model checking ---

def cmc_hide_internal_Actions(folder, autbase, ids):
	"""Hide the actions that are not in any of the procsactsets of the processes in ids.
	Do not hide accept actions."""
	global procsactsets

	if os.path.isfile(os.path.join(folder, autbase + "_hidden.aut")):
		os.remove(os.path.join(folder, autbase + "_hidden.aut"))

	actset = set([])
	for i in ids:
		actset |= procsactsets[i]

	# output file
	outFile = open(os.path.join(folder, autbase + "_hidden.aut"), 'w')
	
	first = True
	for transline in open(os.path.join(folder, autbase + ".aut")):
		if first:
			# first copy header
			outFile.write(transline)
			first = False
		else:
			transsplit = transline.split('"')
			src = transsplit[0].split(',')
			src = src[0][1:]
			act = transsplit[1]
			tgt = transsplit[2].split(',')
			tgt = tgt[1]
			if tgt[0] == ' ':
				tgt = tgt[1:]
			tgt = tgt.split(')')
			tgt = tgt[0]
			# remove quotes
			act = act.replace('\'', '')
			act = act.replace('"', '')
			# remove spaces
			act = act.replace(' ', '')
			if act in actset or act == ACCEPT:
				outFile.write('(' + src + ', "' + act + '", ' + tgt + ')\n')
			else:
				outFile.write('(' + src + ', "tau", ' + tgt + ')\n')
	outFile.close()

def cmc_hide_nonproc_Actions(folder, autbase, prefix):
	"""Hide the actions not prefixed with 'prefix' or ICC_BOTHPROC_PREFIX in the given .aut file, and write the result.
	If 'prefix' refers to previous process, also do not hide negations of actions.
	Before hiding, rewrite ICC_BOTHPROC_PREFIX to 'prefix'.
	Do not hide accept actions, remove (non-negative) prefix from them."""
	if os.path.isfile(os.path.join(folder, autbase + "_hidden.aut")):
		os.remove(os.path.join(folder, autbase + "_hidden.aut"))

	# output file
	outFile = open(os.path.join(folder, autbase + "_hidden.aut"), 'w')
	
	first = True
	for transline in open(os.path.join(folder, autbase + ".aut")):
		if first:
			# first copy header
			outFile.write(transline)
			first = False
		else:
			transsplit = transline.split('"')
			src = transsplit[0].split(',')
			src = src[0][1:]
			act = transsplit[1]
			tgt = transsplit[2].split(',')
			tgt = tgt[1]
			if tgt[0] == ' ':
				tgt = tgt[1:]
			tgt = tgt.split(')')
			tgt = tgt[0]
			# remove quotes
			act = act.replace('\'', '')
			act = act.replace('"', '')
			# remove spaces
			act = act.replace(' ', '')
			if act.startswith(ICC_BOTHPROC_PREFIX):
				act = act.replace(ICC_BOTHPROC_PREFIX, prefix)
			negcheck = False
			if prefix == ICC_PREVPROC_PREFIX:
				negcheck = act.startswith(ICC_NOTPREVPROC_PREFIX)
			if act == ICC_PREVPROC_PREFIX + ACCEPT:
				act = ACCEPT
			if act.startswith(prefix) or negcheck or act == ACCEPT:
				outFile.write('(' + src + ', "' + act + '", ' + tgt + ')\n')
			else:
				outFile.write('(' + src + ', "tau", ' + tgt + ')\n')
	outFile.close()

def cmc_rename_proc_Actions(folder, autbase, prefix):
	"""Remove the 'prefix' and ICC_BOTHPROC_PREFIX from the actions in the given .aut file, and write the result."""
	if os.path.isfile(os.path.join(folder, autbase + "_final.aut")):
		os.remove(os.path.join(folder, autbase + "_final.aut"))

	# output file
	outFile = open(os.path.join(folder, autbase + "_final.aut"), 'w')
	
	first = True
	for transline in open(os.path.join(folder, autbase + ".aut")):
		if first:
			# first copy header
			outFile.write(transline)
			first = False
		else:
			transsplit = transline.split('"')
			src = transsplit[0].split(',')
			src = src[0][1:]
			act = transsplit[1]
			tgt = transsplit[2].split(',')
			tgt = tgt[1]
			if tgt[0] == ' ':
				tgt = tgt[1:]
			tgt = tgt.split(')')
			tgt = tgt[0]
			# remove quotes
			act = act.replace('\'', '')
			act = act.replace('"', '')
			# remove spaces
			act = act.replace(' ', '')
			if act.startswith(prefix):
				act = act.replace(prefix, '')
			elif act.startswith(ICC_BOTHPROC_PREFIX):
				act = act.replace(ICC_BOTHPROC_PREFIX, '')
			outFile.write('(' + src + ', "' + act + '", ' + tgt + ')\n')
	outFile.close()

def cmc_constructDependency():
	global prop_dependency, prop_priority, procs, syncrules, procsactsets, nontrivialpropactions
	
	# introduce in every procsactset the action 'tau':
	for i in range(0,len(procsactsets)):
		procsactsets[i].add('tau')
	tocheck = set([i for i in range(0,len(procs)-1)])
	# start from property. obtain the set of 'non-trivial' actions
	nontrivialpropactions = set([])
	for s, v in procs[len(procs)-1].items():
		for a, tgts in v.items():
			if tgts != set([s]):
				nontrivialpropactions.add(a)
	# identify set of procs directly depending on non-trivial property actions
	newdepset = set([])
	for pid in range(0,len(procs)-1):
		if procsactsets[pid] & nontrivialpropactions != set([]):
			newdepset.add(pid)
			tocheck.remove(pid)
	prop_dependency.append(newdepset)
	lastdepset = newdepset
	# check remainder of procs
	while tocheck != set([]):
		newdepset = set([])
		for i in range(0,len(syncrules)):
			for a, v in syncrules[i].items():
				for (vect, act) in v:
					# is there an involved proc that is still to be checked?
					unchecked_proc = False
					first_active_checked = -1
					for j in range(0,len(procs)-1):
						if vect[j] != '*':
							if j in tocheck:
								unchecked_proc = True
							elif j in lastdepset and first_active_checked == -1:
								first_active_checked = j
					if unchecked_proc and first_active_checked != -1:
						# suitable vector. find dependent processes
						matching_params = set([])
						for a1 in procsactsets[first_active_checked]:
							if a1 == vect[first_active_checked] + action.getParams(a1):
								matching_params.add(action.getParams(a1))
						# check whether rule can be enabled
						unchecked_enabledprocs = set([])
						for j in range(0,len(procs)-1):
							if vect[j] != '*' and j != first_active_checked:
								unmatched_params = set([])
								for pa in matching_params:
									if vect[j] + pa not in procsactsets[j]:
										unmatched_params.add(pa)
								matching_params -= unmatched_params
								if matching_params == set([]):
									break
								elif j in tocheck:
									unchecked_enabledprocs.add(j)
						if matching_params != set([]):
							# rule is enabled. move related unchecked procs to newdepset
							newdepset |= unchecked_enabledprocs
							tocheck -= newdepset
		# next set computed. add it to prop_dependency
		if newdepset != set([]):
			prop_dependency.append(newdepset)
			lastdepset = newdepset
		else:
			# the remainder of tocheck forms a class on it own
			prop_dependency.append(tocheck)
			tocheck = set([])
	prop_priority = {}
	priocounter = 0
	for S in prop_dependency:
		for s in S:
			prop_priority[s] = priocounter
		priocounter += 1
	#print(prop_priority)

def cmc_createCounterexample_LTS():
	"""create and return a counter-example LTS for the current process in the current cmc configuration, based on the state space assumed to be stored as 'check.aut'"""
	# hide actions in file
	cmc_hide_nonproc_Actions(network.folder, "check", ICC_CURRENTPROC_PREFIX)
	# minimise result with weak trace equivalence
	cmc_weaktrace_minimise_LTS("check_hidden")
	# rename remaining actions to originals
	cmc_rename_proc_Actions(network.folder, "check_hidden_wtmin", ICC_CURRENTPROC_PREFIX)
	# read result
	[h,v,a] = aut.read(network.folder, "check_hidden_wtmin_final.aut")
	# make sure ACCEPT only occurs on selfloops. rename other ACCEPT occurrences to tau
# 	for s, vect in v.items():
# 		out = vect.get(ACCEPT)
# 		if out != None:
# 			if out != set([s]):
# 				vect.pop(ACCEPT)
# 				vect['tau'] = out
	openset = deque([h[0]])
	closedset = set([h[0]])
	nrtrans = int(h[1])
	newv = {}
	while len(openset) > 0:
		s = openset.popleft()
		out = v.get(s,{})
		newout = {}
		for a, tgts in out.items():
			if a != ACCEPT:
				newout[a] = tgts
				nrtrans += len(tgts)
				for tgt in tgts:
					if tgt not in closedset:
						openset.append(tgt)
						closedset.add(tgt)
			else:
				newout[a] = set([s])
				nrtrans += 1
		if newout != {}:
			newv[s] = newout
	#prune parts that cannot reach accepting states
	return cmc_prune_LTS([h[0],str(nrtrans),str(len(closedset))],newv)

def cmc_createConstraint(i):
	"""create and return a constraint for the process at position i in the current cmc configuration, based on the state space assumed to be stored as 'check.aut'"""
	global procsactsets
	# hide actions in file of all processes accept previous (and both)
	cmc_hide_nonproc_Actions(network.folder, "check", ICC_PREVPROC_PREFIX)
	# minimise result with weak trace equivalence
	cmc_weaktrace_minimise_LTS("check_hidden")
	# rename remaining actions to originals
	cmc_rename_proc_Actions(network.folder, "check_hidden_wtmin", ICC_PREVPROC_PREFIX)
	# read result
	[h,v,a] = aut.read(network.folder, "check_hidden_wtmin_final.aut")
	nrstates = int(h[2])
	nrtrans = int(h[1])
	# new sink state
	sinkstate = h[2]
	nrstates += 1
	openset = deque([h[0]])
	closedset = set([h[0]])
	onlyfalsenegatives = True
	accept_seen = False
	while len(openset) > 0:
		s = openset.popleft()
		out = v.get(s,{})
		for a, tgts in out.items():
			if not a.startswith(ICC_NOTPREVPROC_PREFIX):
				for tgt in tgts:
					if tgt not in closedset:
						openset.append(tgt)
						closedset.add(tgt)
			if a == ACCEPT:
				accept_seen = True
		# add transitions to sink state
		negated_actions = set([])
		for a in procsactsets[i] - set([ACCEPT]):
			if out.get(a) == None and out.get(ICC_NOTPREVPROC_PREFIX + a) == None:
				out[a] = set([sinkstate])
				nrtrans += 1
			elif out.get(ICC_NOTPREVPROC_PREFIX + a) != None:
				negated_actions.add(ICC_NOTPREVPROC_PREFIX + a)
				if out.get(a) == None:
					# we found a negative action without its positive counter-part from the same state
					onlyfalsenegatives = False
		# add accept loop
		if out.get(ICC_NOTPREVPROC_PREFIX + ACCEPT) == None and out.get(ACCEPT) == None:
			out[ACCEPT] = set([s])
			nrtrans += 1
		# remove negated actions
		for a in negated_actions:
			outlabel = out.get(a)
			nrtrans -= len(outlabel)
			out.pop(a)
		v[s] = out
	if not onlyfalsenegatives or not accept_seen:
		# add transitions for the new sinkstate
		outgoing = {}
		for a in procsactsets[i]:
			outgoing[a] = set([sinkstate])
			nrtrans += 1
		outgoing[ACCEPT] = set([sinkstate])
		nrtrans += 1
		v[sinkstate] = outgoing
		# make new header
		h = [h[0],str(nrtrans),str(nrstates)]
		aut.write(network.folder, h, v, "constraint")
		# minimise result with trace equivalence
		cmc_trace_minimise_LTS("constraint")
	#return not onlyfalsenegatives or not accept_seen
	return not accept_seen

# hide actions of process i w.r.t. given LTS ids
# "accept" is considered a special keyword indicating accepting states.
# hiding this action is not allowed!
def cmc_createHidden_LTS(i, ids, outputtail):
	global procfiles, procsactsets, hideactions
	# set hiding set
	hideactions = copy.deepcopy(network.procsactsets[i])
	for id in ids:
		hideactions -= network.procsactsets[id]
	hideactions = list(hideactions)
	# hide actions in file
	hideActions(network.folder, network.procfiles[i][:-4], {ACCEPT}, outputtail)

def cmc_branching_minimise_LTS(procfile):
	# minimise LTS
	if os.path.isfile(os.path.join(network.folder, procfile + "_min.aut")):
		os.remove(os.path.join(network.folder, procfile + "_min.aut"))
	rlt = subprocess.Popen(["ltsconvert", "--equivalence=branching-bisim", "--tau=i", os.path.join(network.folder, procfile + ".aut"), os.path.join(network.folder, procfile + "_min.aut")], stderr=subprocess.PIPE)
	out, err = rlt.communicate()
	#print(out)
	#print(err)

def cmc_strong_minimise_LTS(procfile):
	# minimise LTS
	if os.path.isfile(os.path.join(network.folder, procfile + "_stmin.aut")):
		os.remove(os.path.join(network.folder, procfile + "_stmin.aut"))
	rlt = subprocess.Popen(["ltsconvert", "--equivalence=bisim", os.path.join(network.folder, procfile + ".aut"), os.path.join(network.folder, procfile + "_stmin.aut")], stderr=subprocess.PIPE)
	out, err = rlt.communicate()
	#print(out)
	#print(err)

def cmc_weaktrace_minimise_LTS(procfile):
	# minimise LTS
	if os.path.isfile(os.path.join(network.folder, procfile + "_wtmin.aut")):
		os.remove(os.path.join(network.folder, procfile + "_wtmin.aut"))
# 	rlt = subprocess.Popen(["ltsconvert", "--equivalence=branching-bisim", os.path.join(network.folder, procfile + ".aut"), os.path.join(network.folder, procfile + "_btmin.aut")], stderr=subprocess.PIPE)
# 	out, err = rlt.communicate()
# 	print(out)
# 	print(err)
	rlt = subprocess.Popen(["ltsconvert", "--equivalence=weak-trace", os.path.join(network.folder, procfile + ".aut"), os.path.join(network.folder, procfile + "_wtmin.aut")], stderr=subprocess.PIPE)
	out, err = rlt.communicate()
	#print(out)
	#print(err)

def cmc_trace_minimise_LTS(procfile):
	# minimise LTS
	if os.path.isfile(os.path.join(network.folder, procfile + "_tmin.aut")):
		os.remove(os.path.join(network.folder, procfile + "_tmin.aut"))
	rlt = subprocess.Popen(["ltsconvert", "--equivalence=trace", os.path.join(network.folder, procfile + ".aut"), os.path.join(network.folder, procfile + "_tmin.aut")], stderr=subprocess.PIPE)
	out, err = rlt.communicate()
	#print(out)
	#print(err)

# convention:
# - state 0 is initial state
# - state 1 is an accepting sink state (allowing all behaviour)
# - state 2 is a non-accepting state, with transitions for all behaviour going to state 1
# def cmc_createInitialConstraintsLTS(i):
# 	"""create initial constraints LTS for process i"""
# 	global initial_constraintsLTSs
# 	
# 	cLTSheader = ['0', str(3*len(network.procsactsets[i])+2), '3']
# 	cLTStrans = {}
# 	first_outgoing = {}
# 	second_outgoing = {}
# 	third_outgoing = {}
# 	for a in network.procsactsets[i]:
# 		first_outgoing[a] = set(['1'])
# 		second_outgoing[a] = set(['1'])
# 		third_outgoing[a] = set(['1'])
# 	first_outgoing['"accept"'] = set(['0'])
# 	second_outgoing['"accept"'] = set(['1'])
# 	cLTStrans['0'] = first_outgoing
# 	cLTStrans['1'] = second_outgoing
# 	cLTStrans['2'] = third_outgoing
# 	initial_constraintsLTSs[i] = (cLTSheader, cLTStrans)

def cmc_createInitialConstraintsLTS(i):
	"""create minimal initial constraints LTS for process i"""
	global constraintsLTStree, basic_constraintsLTSs
	
	cLTSheader = ['0', str(len(network.procsactsets[i])+1), '1']
	cLTStrans = {}
	outgoing = {}
	for a in network.procsactsets[i]:
		outgoing[a] = {'0'}
	outgoing[ACCEPT] = {'0'}
	cLTStrans['0'] = outgoing
	constraintsLTStree[i][0] = (cLTSheader, cLTStrans)
	basic_constraintsLTSs[i] = copy.deepcopy((cLTSheader, cLTStrans))

def cmc_minimiseConstraintsLTSOnFile(ipos, filename, checklist, updateref):
	"""minimise LTS in .aut file using strong bisimulation, store result in constraintsLTS tree. If updateref == True, also update reference in constraintsLTSs"""
	global constraintsLTSs
	if os.path.isfile(os.path.join(network.folder, "constraints_stmin.aut")):
		os.remove(os.path.join(network.folder, "constraints_stmin.aut"))
	rlt = subprocess.Popen(["ltsconvert", "--equivalence=bisim", os.path.join(network.folder, filename + ".aut"), os.path.join(network.folder, "constraints_stmin.aut")], stderr=subprocess.PIPE)
	out, err = rlt.communicate()
	#print(out)
	#print(err)
	[h,v,a] = aut.read(network.folder, "constraints_stmin.aut")
	insertSingleConstraintsLTS((h,v), ipos, checklist)
	if updateref:
		constraintsLTSs[checklist[ipos]] = (h,v)

def cmc_trace_minimiseConstraintsLTSOnFile(ipos, filename, checklist, updateref):
	"""minimise LTS in .aut file using weak trace equivalence, store result in constraintsLTS tree. If updateref == True, also update reference in constraintsLTSs"""
	global constraintsLTSs
	if os.path.isfile(os.path.join(network.folder, "constraints_tmin.aut")):
		os.remove(os.path.join(network.folder, "constraints_tmin.aut"))
	rlt = subprocess.Popen(["ltsconvert", "--equivalence=trace", os.path.join(network.folder, filename + ".aut"), os.path.join(network.folder, "constraints_tmin.aut")], stderr=subprocess.PIPE)
	out, err = rlt.communicate()
	#print(out)
	#print(err)
	[h,v,a] = aut.read(network.folder, "constraints_tmin.aut")
	insertSingleConstraintsLTS((h,v), ipos, checklist)
	if updateref:
		constraintsLTSs[checklist[ipos]] = (h,v)

# def cmc_minimiseConstraintsLTS(i):
# 	"""minimise constraints LTS of process i using strong bisimulation"""
# 	global constraintsLTSs, min_constraintsLTSs
# 	aut.write(network.folder, constraintsLTSs[i][0], constraintsLTSs[i][1], "constraints")
# 	# minimise LTS
# 	rlt = subprocess.Popen(["ltsconvert", "--equivalence=bisim", os.path.join(network.folder, "constraints.aut"), os.path.join(network.folder, "constraints_stmin.aut")], stderr=subprocess.PIPE)
# 	out, err = rlt.communicate()
# #	print(out)
# #	print(err)
# 	[h,v,a] = aut.read(network.folder, "constraints_stmin.aut")
# 	min_constraintsLTSs[i] = (h,v)

def cmc_extendConstraintsLTS(i, ipos, newconstraint, initial):
	"""extend the constraintsLTS of process i, given the semi-composition of the checkLTS of process i with the successor in the current configuration.
	If initial = True, directly update the initial constraints LTS instead of the current used one."""
	# the check LTS of i, the semi-composition, and the constraints LTS of i are deterministic
	# if backtrack == True and accepting states were reached, an extended version of the semi-composition should be used for subsequent checks
	global constraintsupdateprocs, constraintsupdateheaders, constraintsLTSs, cmc_constraintsconstr_syncrules, cmc_constraintsconstr_syncactions, cmc_checklist

	# construct a suitable network to obtain a new constraints LTS via parallel composition
	for j in range(0,len(constraintsupdateprocs)):
		if j != i and j != len(constraintsupdateprocs)-1:
			constraintsupdateprocs[j] = {}
			constraintsupdateheaders[j] = ['0','0','0']
		elif j == i:
			constraintsupdateprocs[j] = newconstraint[1]
			constraintsupdateheaders[j] = newconstraint[0]
		else:
			if initial:
				constraintsupdateprocs[j] = constraintsLTStree[i][0][1]
				constraintsupdateheaders[j] = constraintsLTStree[i][0][0]
			else:
				constraintsupdateprocs[j] = constraintsLTSs[i][1]
				constraintsupdateheaders[j] = constraintsLTSs[i][0]
	# construct the new constraints LTS
	if os.path.isfile(os.path.join(network.folder, "constraints.aut")):
		os.remove(os.path.join(network.folder, "constraints.aut"))
	generateLTS(constraintsupdateheaders, constraintsupdateprocs, network.procsactsets, cmc_constraintsconstr_syncrules[i], cmc_constraintsconstr_syncactions[i], os.path.join(network.folder, "constraints"), opt.quiet, config.outputobject, 0, [i, len(constraintsupdateprocs)-1], 0, False, True, False)
	# minimise result using strong bisimulation, and store result in constraintsLTS tree
	if initial:
		cmc_trace_minimiseConstraintsLTSOnFile(0, "constraints", [i], False)
	else:
		cmc_trace_minimiseConstraintsLTSOnFile(ipos, "constraints", cmc_checklist, True)

# def cmc_extendConstraintsLTS(i, maxid, allow):
# 	"""extend the constraintsLTS of process i, given the id of the final state reached in the checkLTS of process i. There are two options: disable the transition after maxid and extensions (allow==False), or still allow extensions of after maxid (allow=True)"""
# 	# maxid is the last state that was reachable in the check LTS of process i, constraints LTS i is a deterministic LTS
# 	global checkprocs, constraintsLTSs
# 	
# 	#print(str(i) + ": " + str(t) + " " + str(allow))
# 	# get the relevant checkproc LTS
# 	checkLTS = checkprocs[i]
# 	# get constraintsLTS info
# 	(header, trans) = constraintsLTSs[i]
# 	nrstates = int(header[2])
# 	nrtrans = int(header[1])
# 	stop = False
# 	# current state
# 	current = '0'
# 	for aid in range(0,len(t)-1):
# 		outgoing = trans.get(current,{})
# 		a_tgts = outgoing.get(t[aid], set([]))
# 		# if there is no suitable target state, this trace should not be accepted, and we can stop
# 		if a_tgts == set([]):
# 			stop = True
# 			break
# 		tgt = next(iter(a_tgts))
# 		if int(tgt) <= 2:
# 			# redirect transition to a new state.
# 			outgoing[t[aid]] = set([str(nrstates)])
# 			trans[current] = outgoing
# 			# add transitions for all actions to the accepting state 1
# 			tgt_outgoing = {}
# 			for a in network.procsactsets[i]:
# 				tgt_outgoing[a] = set(['1'])
# 				nrtrans += 1
# 			# add an accepting self-loop only if the original tgt was accepting
# 			if tgt == '1':
# 				tgt_outgoing['"accept"'] = set([str(nrstates)])
# 				nrtrans += 1
# 			trans[str(nrstates)] = tgt_outgoing
# 			# move state
# 			current = str(nrstates)
# 			nrstates += 1
# 		else:
# 			# move state
# 			current = tgt
# 	# final step of t. depending on allow, either disable final step or not but make it go to a non-accepting state
# 	if not stop:
# 		outgoing = trans.get(current,{})
# 		if len(t) == 0:
# 			# special case: trace has length 0. Remove the 'accept' selfloop of the initial state
# 			del outgoing['"accept"']
# 			trans[current] = outgoing
# 			nrtrans -= 1
# 		else:
# 			a = t[len(t)-1]
# 			a_tgts = outgoing.get(a,set([]))
# 			if a_tgts != set([]):
# 				tgt = next(iter(a_tgts))
# 				if not allow:
# 					# completely disable this action
# 					del outgoing[a]
# 					trans[current] = outgoing
# 					nrtrans -= 1
# 				elif tgt != '2':
# 					# redirect transition to state 2
# 					outgoing[a] = set(['2'])
# 					trans[current] = outgoing
# 	# update header
# 	constraintsLTSs[i] = ([header[0], str(nrtrans), str(nrstates)], trans)

# def cmc_update_tree(i):
# 	"""update the constraints tree from position i in the current check configuration"""
# 	global cmc_checktree, cmc_checklist, constraintsLTSs, constraintsLTS_is_extended
# 
# 	seqname = "cons_"
# 	children1 = cmc_checktree
# 	for j in range(0,len(cmc_checklist)-1):
# 		cid = cmc_checklist[j][0]
# 		seqname += str(cid) + "_"
# 		children2 = children1[0].get(cid,({},set([])))
# 		if children2[0] == {}:
# 			children1[0][cid] = ({},set([]))
# 		if j >= i and constraintsLTS_is_extended[cid]:
# 			children1[0][cid] = (children2[0],children2[1].add(cid))
# 			# possibly add initial constraints LTS to root of tree
# 			if j == 0:
# 				cmc_checktree[1].add(cid)
# 			aut.write(network.folder, constraintsLTSs[cmc_checklist[j][0]][0], constraintsLTSs[cmc_checklist[j][0]][1], seqname + network.procfiles[cmc_checklist[j][0]][:-4])
# 			# no longer needed to keep track of extension
# 			constraintsLTS_is_extended[cid] = False
# 		children1 = children2

# def cmc_add_to_constraints_updates(i, stems_from_shift):
# 	"""add an update to the constraints updates list"""
# 	global cmc_checklist, cmc_constraints_updates
# 	
# 	if i < len(cmc_checklist)-1:
# 		f = cmc_constraints_updates[cmc_checklist[i+1]]
# 		if f > i:
# 			cmc_constraints_updates[cmc_checklist[i+1]] = i

# def cmc_move_constraints_updates(i):
# 	"""move the constraints updates recorded for position i in the current check configuration one place to the right (unless the end has been reached)"""
# 	global cmc_checklist, cmc_constraints_updates
# 
# 	cid = cmc_checklist[i]
# 	if i < len(cmc_checklist)-1:
# 		cidp = cmc_checklist[i+1]
# 		f1 = cmc_constraints_updates[cid]
# 		f2 = cmc_constraints_updates[cidp]
# 		cmc_constraints_updates[cidp] = min(f1,f2)
# 	cmc_constraints_updates[cid] = len(network.procs)

# def cmc_find_new_initial_constraints_LTS(i, remove_pos):
# 	"""find a new initial constraints LTS for the process at position i in the current check configuration.
# 	   Remove any files containing constraints that are no longer valid (i.e. refer to constraints at a position higher than
# 	   or equal to remove_pos)"""
# 	global cmc_checktree, cmc_checklist, initial_constraintsLTSs, constraintsLTSs, constraintsLTS_is_extended, cmc_constraintsdep
# 
# 	cid = cmc_checklist[i][0]
# 	seqname = "cons_"
# 	last_found = "cons_"
# 	last_found_pos = -1
# 	children1 = cmc_checktree
# 	k = 0
# 	while children1[0] != {} and k < i:
# 		ckd = cmc_checklist[k][0]
# 		children2 = children1[0].get(ckd,({},set([])))
# 		seqname += str(ckd) + "_"
# 		if cid in children2[1]:
# 			if k < remove_pos:
# 				last_found = copy.deepcopy(seqname)
# 				last_found_pos = k
# 			else:
# 				# this part of the check configuration has been reset. stored file is no longer relevant
# 				os.remove(os.path.join(network.folder, seqname + network.procfiles[cid][:-4]))
# 				S = children2[1]
# 				S.remove(i)
# 				children2 = (children2[0],S)
# 		children1 = children2
# 		k += 1
# 	if last_found == "cons_":
# 		# check for stored initial constraints LTS
# 		if cid in cmc_checktree[1]:
# 			last_found += str(cid) + "_"
# 		else:
# 			cmc_createInitialConstraintsLTS(cid)
# 			cmc_createInitialMinConstraintsLTS(cid)
# 			cmc_constraintsdep[cid] = -1
# 	if last_found != "cons_":
# 		# read
# 		filename = last_found + network.procfiles[cid][:-4]
# 		[h,v,a] = aut.read(network.folder, filename + ".aut")
# 		initial_constraintsLTSs[cid] = (h,v)
# 		cmc_minimiseInitialConstraintsLTSOnFile(cid, os.path.join(network.folder, filename + ".aut"))
# 		cmc_constraintsdep[cid] = last_found_pos

# def cmc_process_remaining_constraints_updates(i):
# 	"""before a shift is done, process any remaining updates performed in the current check configuration, starting at position i"""
# 	global cmc_checklist, initial_min_constraintsLTSs, initial_constraintsLTSs, constraintsLTSs, min_constraintsLTSs, constraintsLTS_is_extended, cmc_constraintsdep, cmc_constraints_updates
# 
# 	for j in range(i,len(cmc_checklist)):
# 		cid = cmc_checklist[j][0]
# 		(t,f) = cmc_constraints_updates[cid]
# 		if f != len(network.procs):
# 			# possibly find new initial constraints LTS
# 			if f <= cmc_constraintsdep[cid]:
# 				cmc_find_new_initial_constraints_LTS(j,f)
# 			# update current constraints LTS
# 			if constraintsLTS_is_extended[cid]:
# 				constraintsLTSs[cid] = copy.deepcopy(initial_constraintsLTSs[cid])
# 				min_constraintsLTSs[cid] = copy.deepcopy(initial_min_constraintsLTSs[cid])
# 				# constraints LTS is no longer extended
# 				constraintsLTS_is_extended[cid] = False
# 			# update the constraints updates list
# 			cmc_move_constraints_updates(j)

# def cmc_update_constraints_LTSs(i):
# 	"""if necessary, find new initial constraints LTS for process at position i in current check configuration, and/or update current constraints LTS"""
# 	global cmc_checktree, cmc_checklist, initial_min_constraintsLTSs, initial_constraintsLTSs, constraintsLTSs, min_constraintsLTSs, constraintsLTS_is_extended, cmc_constraintsdep, cmc_constraints_updates
# 
# 	cid = cmc_checklist[i][0]
# 	(t,f) = cmc_constraints_updates[cid]
# 	if t != len(network.procs) or f != len(network.procs):
# 		# condition for updating the initial constraints LTS
# 		if t < len(network.procs) or f <= cmc_constraintsdep[cid]:
# 			# shift happened somewhere in the checklist. check for new initial constraints LTS
# 			cmc_find_new_initial_constraints_LTS(i,f)
# 		if t == i or f < len(network.procs):
# 			# on this position a shift took place. Set current constraints LTS to the initial constraints LTS
# 			constraintsLTSs[cid] = copy.deepcopy(initial_constraintsLTSs[cid])
# 			min_constraintsLTSs[cid] = copy.deepcopy(initial_min_constraintsLTSs[cid])
# 			# constraints LTS is no longer extended
# 			constraintsLTS_is_extended[cid] = False
# 		# update the constraints updates list
# 		cmc_move_constraints_updates(i)

def cmc_prune_LTS(h, v):
	"""prune the given LTS. This involves checking which parts can reach accepting states. Parts that cannot are removed."""
	# construct backward reachability information
	backreach = {}
	for s, strans in v.items():
		for a, tgts in strans.items():
			for tgt in tgts:
				sset = backreach.get(tgt,set([]))
				sset.add(s)
				backreach[tgt] = sset
	# openset for reachability analysis
	openset = deque([])
	visited = set([])
	# all accepting states should be added to openset and visited
	for i in range(0,int(h[2])):
		s = str(i)
		sout = v.get(s,{})
		if sout.get(ACCEPT) is not None:
			visited.add(s)
			openset.append(s)
	# the main analysis
	while len(openset) > 0:
		s = openset.popleft()
		sout = backreach.get(s,set([]))
		for t in sout:
			if t not in visited:
				openset.append(t)
				visited.add(t)
	# determine new state ids
	idmap = {}
	# set initial state to '0'
	idmap[h[0]] = '0'
	statecounter = 1
	for s in visited:
		if idmap.get(s) is None:
			idmap[s] = str(statecounter)
			statecounter += 1
	# create new, pruned LTS
	v2 = {}
	transcount = 0
	actions = set([])
	for s, strans in v.items():
		if s in visited:
			sout = {}
			for a, tgts in strans.items():
				newtgts = set([])
				for tgt in tgts:
					if tgt in visited:
						newtgts.add(idmap[tgt])
				if newtgts != set([]):
					sout[a] = newtgts
					actions.add(a)
					transcount += len(newtgts)
			if sout != {}:
				v2[idmap[s]] = sout
	h2 = ['0',str(transcount),str(len(visited))]
	return (h2,v2,actions)

def cmc_checklist_insert_abstract_property_LTS(i):
	"""insert an abstract property LTS for process at position i in current check configuration"""
	global cmc_checklist, propertyLTSs, checkprocs, checkheaders
	# insert an abstracted, minimised version of the property LTS. if it does not yet exist, create it first

	pid = cmc_checklist[i]
# 	if propertyLTSs[pid] == ():
# 		propproclist = sorted([j in cmc_checklist[:i+1]])
# 		propprocliststring = ""
# 		for j in range(0,len(propproclist)):
# 			propprocliststring += str(propproclist[j]) + "_"
# 		propprocliststring = propprocliststring[:-1]
# 		if not os.path.isfile(os.path.join(network.folder, network.procfiles[len(network.procs)-1][:-4] + "_hidden" + propprocliststring + "_min.aut")):
# 			S = set(propproclist)
# 			cmc_createHidden_LTS(len(network.procs)-1, S, propprocliststring)
# 			cmc_minimiseLTS(network.procfiles[len(network.procs)-1][:-4] + "_hidden" + propprocliststring)
# 		[h,v,a] = aut.read(network.folder, network.procfiles[len(network.procs)-1][:-4] + "_hidden" + propprocliststring + "_min.aut")
# 		propertyLTSs[pid] = (h,v)
# 	checkprocs[len(network.procs)-1] = propertyLTSs[pid][1]
# 	checkheaders[len(network.procs)-1] = propertyLTSs[pid][0]
	if propertyLTSs[pid] == ():
		propproclist = cmc_checklist[:i+1]
		cmc_createHidden_LTS(len(network.procs)-1, set(propproclist), "")
		cmc_weaktrace_minimise_LTS(network.procfiles[len(network.procs)-1][:-4] + "_hidden")
		[h,v,a] = aut.read(network.folder, network.procfiles[len(network.procs)-1][:-4] + "_hidden_wtmin.aut")

		#copyfile(os.path.join(network.folder, procfiles[len(procs)-1][:-4] + "_hidden_wtmin.aut"), os.path.join(network.folder, procfiles[len(procs)-1][:-4] + str(propproclist) + "_hidden_wtmin.aut"))

		# make sure ACCEPT only occurs on selfloops
# 		for s, vect in v.items():
# 			out = vect.get(ACCEPT)
# 			if out != None:
# 				if out != set([s]):
# 					vect.pop(ACCEPT)
# 					vect['tau'] = out
		openset = deque([h[0]])
		closedset = set([h[0]])
		nrtrans = int(h[1])
		newv = {}
		while len(openset) > 0:
			s = openset.popleft()
			out = v.get(s,{})
			newout = {}
			for a, tgts in out.items():
				if a != ACCEPT:
					newout[a] = tgts
					nrtrans += len(tgts)
					for tgt in tgts:
						if tgt not in closedset:
							openset.append(tgt)
							closedset.add(tgt)
				else:
					newout[a] = set([s])
					nrtrans += 1
			if newout != {}:
				newv[s] = newout
		propertyLTSs[pid] = ([h[0], str(nrtrans), str(len(closedset))],newv)
	checkprocs[len(procs)-1] = propertyLTSs[pid][1]
	checkheaders[len(procs)-1] = propertyLTSs[pid][0]

def determiniseLTS(L, detL):
	"""determinise the given LTS L using the standard powerset construction algorithm, and put the result in detL"""
	Lheader = L[0]
	statecount = 0
	transcount = 0
	htable = {}
	currentstate = tuple([Lheader[0]])
	htable[currentstate] = str(statecount)
	statecount += 1
	openset = deque([['0']])
	openset.popleft()
	openset.append(currentstate)
	while len(openset) > 0:
		currentstate = openset.popleft()
		srcindex = htable.get(currentstate)
		outgoing = {}
		# build up non-det sets of successors
		for s in currentstate:
			outgoings = L[1].get(s,{})
			for a, v in outgoings.items():
				outgoinglabel = outgoing.get(a,set([]))
				outgoing[a] = outgoinglabel | v
		# transform sets of successors into new, unique successors
		detoutgoing = {}
		for a, v in outgoing.items():
			lv = list(v)
			lv.sort()
			vstate = tuple(lv)
			index = htable.get(vstate)
			if index is None:
				htable[vstate] = str(statecount)
				index = statecount
				statecount += 1
				# add new state to openset
				openset.append(vstate)
			detoutgoing[a] = {str(index)}
			transcount += 1
		# add outgoing transitions to det LTS
		detL[1][srcindex] = detoutgoing
	# set header of detL
	detL[0] = ['0', str(transcount), str(statecount)]


def identifySCCs(L, SCCdict, SCCs):
	"""Identify the SCC in L, keep track for each state to which SCC it belongs in 'SCCdict', and store the SCCs in 'SCCs'"""
	# call stack
	callstack = []
	# scc stack
	sccstack = []
	sccstackset = set([])
	# numbers
	number = {}
	scc_index = 0
	scc_count = 0
	# iterate over all states
	for j in range(0,int(L[0][2])):
		s = str(j)
		if number.get(s) is None:
			targets = set([])
			outgoing = L[1].get(s,{})
			for a, tgt in outgoing.items():
				targets.add(tgt)
			callstack.append([s,list(targets)])
				
			while len(callstack) > 0:
				[s,targets] = peek(callstack)
				if (number.get(s) is None ):
					number[s] = scc_index
					SCCdict[s] = scc_index
					scc_index += 1
					sccstack.append(s)
					sccstackset.add(s)
				# walk over targets
				while len(targets) > 0:
					t = peek(targets)
					if number.get(t) is None:
						# add successor to call stack
						ttargets = set([])
						toutgoing = L[1].get(t,{})
						for a, tgt in toutgoing.items():
							ttargets.add(tgt)
						callstack.append([t,list(ttargets)])
						break
					elif t in sccstackset:
						r = SCCdict.get(s)
						SCCdict[s] = min(r, number.get(t))
					targets.pop()
				if len(targets) == 0:
					# is s a root state?
					if SCCdict[s] == number[s]:
						# a new SCC has been found
						scc_count += 1
						if len(sccstack) > 0:
							t = sccstack.pop()
							sccstackset.remove(t)
						while t != s and len(sccstack) > 0:
							SCCdict[t] = SCCdict[s]
							t = sccstack.pop()
							sccstackset.remove(t)
					callstack.pop()
					# update predecessor
					if len(callstack) > 0:
						[t,_] = peek(callstack)
						SCCdict[t] = min(SCCdict[t],SCCdict[s])
	# a hash table to map SCC id's to consecutive id's
	scchtable = {}
	scc_newidcount = 0
	# update SCCdict
	for j in range(0,int(L[0][2])):
		s = str(j)
		sSCC = SCCdict.get(s)
		# lookup the new SCC id
		scc_newid = scchtable.get(sSCC)
		if scc_newid is None:
			scchtable[sSCC] = scc_newidcount
			scc_newid = scc_newidcount
			scc_newidcount += 1
		SCCdict[s] = scc_newid		
	# construct the SCCs in 'SCCs'
	for j in range(0,scc_count):
		SCCs.append([0,{}])
	for j in range(0,int(L[0][2])):
		s = str(j)
		sSCC = SCCdict.get(s)
		# update state counter of the corresponding SCC
		SCCs[sSCC][0] += 1
		# identify relevant outgoing transitions
		outgoing = L[1].get(s,{})
		sccoutgoing = {}
		for a, t in outgoing.items():
			if SCCdict.get(t) == sSCC:
				sccoutgoing[a] = t
		SCCs[sSCC][1][s] = sccoutgoing

def getConstraintsLTS(i):
	"""retrieve from the constraintsLTStree the constraints LTS for process at position i in the current configuration. If not existing, insert the initial constraints LTS in the tree and return it"""
	global constraintsLTStree, constraintsLTSs, basic_constraintsLTSs, cmc_checklist
	
	currentlist = constraintsLTStree
	for j in cmc_checklist[:i]:
		if not currentlist[j][1]:
			# add new list at this level
			currentlist[j][1] = [[(),[]] for k in range(0,len(cmc_checklist))]
		currentlist = currentlist[j][1]
	if currentlist[cmc_checklist[i]][0] == ():
		#if i < len(cmc_checklist)-1:
		currentlist[cmc_checklist[i]][0] = copy.deepcopy(constraintsLTStree[cmc_checklist[i]][0])
		#else:
		#	currentlist[cmc_checklist[i]][0] = copy.deepcopy(basic_constraintsLTSs[cmc_checklist[i]])
	return currentlist[cmc_checklist[i]][0]

def existsConstraintsLTS(i, checklist):
	"""does the constraints LTS for process at position i in the given configuration exist in the constraintsLTStree?"""
	global constraintsLTStree, initial_constraintsLTSs
	
	currentlist = constraintsLTStree
	for j in checklist[:i]:
		if not currentlist[j][1]:
			return False
		currentlist = currentlist[j][1]
	return currentlist[checklist[i]][0] != ()

def removeConstraintsLTSs(i, checklist):
	"""remove all constraints LTSs dependent on the constraints of the process at position i in the given configuration. If these do not exist, do nothing"""
	global constraintsLTStree, initial_constraintsLTSs
	
	currentlist = constraintsLTStree
	for j in checklist[:i]:
		currentlist = currentlist[j][1]
		if not currentlist:
			break
	if currentlist:
		currentlist[checklist[i]][1] = []

def removeSingleConstraintsLTS(i):
	"""remove constraints LTS of the process at position i in the current configuration. If it does not exist, do nothing"""
	global constraintsLTStree, initial_constraintsLTSs, cmc_checklist
	
	if i > 0:
		currentlist = constraintsLTStree
		for j in cmc_checklist[:i]:
			currentlist = currentlist[j][1]
			if not currentlist:
				break
		if currentlist:
			currentlist[cmc_checklist[i]][0] = ()

def insertSingleConstraintsLTS(constraint, i, checklist):
	"""insert constraints LTS of the process at position i in the given configuration."""
	global constraintsLTStree, cmc_checklist
	
	currentlist = constraintsLTStree
	for j in checklist[:i]:
		if not currentlist[j][1]:
			currentlist[j][1] = [[(),[]] for k in range(0,len(cmc_checklist))]
		currentlist = currentlist[j][1]
	currentlist[checklist[i]][0] = constraint

def rotateConfiguration(rotatestart, firstprocpos):
	"""rotate the processes in the current configuration starting from position rotatestart until the process currently at firstprocpos is situated at rotatestart"""
	global propertyLTSs, cmc_checklist, checkprocs, checkheaders, abstractcheckprocs, abstractcheckheaders, constraintsLTS_is_extended, nrchecksshift

	for j in range(rotatestart,len(cmc_checklist)):
		propertyLTSs[cmc_checklist[j]] = ()
	# how many steps to move?
	nrsteps = len(cmc_checklist) - firstprocpos
	# move
	# create new configuration first
	cmc_checklist_new = copy.deepcopy(cmc_checklist)
	for j in range(rotatestart,len(cmc_checklist)):
		newpos = j + nrsteps
		if newpos >= len(cmc_checklist):
			newpos = rotatestart + (newpos - len(cmc_checklist))
		cmc_checklist_new[newpos] = cmc_checklist[j]
		# possibly reset abstract constructs
		if newpos != j:
			abstractcheckprocs[cmc_checklist_new[j]] = {}
			abstractcheckheaders[cmc_checklist_new[j]] = ['0','0','0']

	# turn
	for j in range(rotatestart,len(cmc_checklist)):
		checkprocs[cmc_checklist_new[j]] = {'0': {ACCEPT: {'0'}}}
		checkheaders[cmc_checklist_new[j]] = ['0','1','1']
		# old position
		oldpos = j - nrsteps
		if oldpos < rotatestart:
			oldpos = len(cmc_checklist) - (rotatestart - oldpos)
		# move constraints LTS?
		if oldpos > 0 and oldpos < j and constraintsLTS_is_extended[cmc_checklist_new[j]]:
			if not existsConstraintsLTS(j, cmc_checklist_new):
				insertSingleConstraintsLTS(copy.deepcopy(getConstraintsLTS(oldpos)), j, cmc_checklist_new)
		# else remove constraints LTS in old position and any dependent constraints LTSs
# 		else:
# 			removeConstraintsLTSs(oldpos)
		if existsConstraintsLTS(j, cmc_checklist_new):
			constraintsLTS_is_extended[cmc_checklist_new[j]] = True
		else:
			constraintsLTS_is_extended[cmc_checklist_new[j]] = False
		# reset shift counter
		#nrchecksshift[j] = 0
	cmc_checklist = cmc_checklist_new

def readCounterexampleActions():
	"""read the counter-example actions stored on disk"""
	actions = set([])
	# read counter-example
	t = [tline for tline in open(os.path.join(network.folder, "check-ce"))]
	# strip newlines and split on ', '
	t = [tr.strip('\n').split(', ') for tr in t]
	for (s,a) in t:
		# remove prefixes
		a = a.replace(ICC_BOTHPROC_PREFIX, '')
		a = a.replace(ICC_PREVPROC_PREFIX, '')
		a = a.replace(ICC_CURRENTPROC_PREFIX, '')
		a = a.replace(ICC_NOTPREVPROC_PREFIX, '')
		if a != 'tau' and a != 'i':
			actions.add(a)
	return actions

def cmc_find_direct_path_actions(h,v):
	"""find and return (a subset of) the set of actions on cycle-free paths leading to accepting states in v"""
	directactions = set([])

	# call stack
	callstack = []
	callstackset = set([])

	# set of states of which we know that a simple path to an accepting state exists
	closed_simple_states = set([])
	closed = set([])
	# keep track of whether we are adding actions in each state
	adding = set([])

	# insert initial state
	out = v.get(h[0],{})
	targets = []
	for a, tgts in out.items():
		for tgt in tgts:
			targets.append((a,tgt))
	callstack.append([h[0], targets])
	callstackset.add(h[0])
	backtracking_mode = False
	# search as long as there are states to be explored
	while len(callstack) > 0:
		[s, trans] = peek(callstack)
		while len(trans) > 0:
			(a,t) = peek(trans)
			# add successor to call stack, if it has not been explored or on the call stack already
			if t not in callstackset and t not in closed and not backtracking_mode:
				targets = []
				out = v.get(t,{})
				for a, tgts in out.items():
					for tgt in tgts:
						targets.append((a,tgt))
				callstack.append([t, targets])
				callstackset.add(t)
				break
			if t in closed_simple_states:
				adding.add(s)
				directactions.add(a)
			# if a is an ACCEPT action, the current state has trivially a path to an accepting state
			elif a == ACCEPT:
				adding.add(s)
			trans.pop()
			if backtracking_mode:
				backtracking_mode = False
		if len(trans) == 0:
			if s in adding:
				adding.remove(s)
				closed_simple_states.add(s)
			closed.add(s)
			callstack.pop()
			callstackset.remove(s)
			backtracking_mode = True
	return directactions

def cmc_construct_network_structures():
	"""construct the network structures required to perform icc"""
	global cmc_syncrules, cmc_syncactions, cmc_constraintsconstr_syncrules, cmc_constraintsconstr_syncactions

	# create extended syncrules for each process in the network. Extensions are needed to allow for
	# correct inclusion of a constraints LTS
	cmc_syncrules = []
	cmc_syncactions = []
	cmc_constraintsconstr_syncrules = []
	cmc_constraintsconstr_syncactions = []
	for i in range(0,len(network.procs)-1):
		cmc_syncrules.append([])
		for j in range(0,len(network.syncrules)):
			cmc_syncrules[i].append({})
			for a, v in network.syncrules[j].items():
				newv = []
				for (vect, act) in v:
					newvect = copy.deepcopy(vect)
					if vect[i] != '*':
						# extend for constraints LTS with action
						newvect.append(vect[i])
					else:
						newvect.append('*')
					newv.append((newvect, act))
				cmc_syncrules[i][j][a] = newv
		# add empty dict for constraints LTS
		cmc_syncrules[i].append({})
		# add syncrules for all actions of process i not already syncing. Let them sync with the constraints LTS
		for a in (network.procsactprefixsets[i] - network.syncactions[i]):
			newvect = []
			for j in range(0,len(network.procs)):
				if j != i:
					newvect.append('*')
				else:
					newvect.append(a)
			newvect.append(a)
			# handle the special case that a=tau. The result should not be tau, but another unique action
			#if a == 'tau':
			#	cmc_syncrules[i][i][a] = [(newvect, 'vtau')]
			#else:
			cmc_syncrules[i][i][a] = [(newvect, a)]
		# copy these rules to cmc_constraintsconstr_syncrules. Both sets of rules are identical for the rules considered so far
		cmc_constraintsconstr_syncrules.append(copy.deepcopy(cmc_syncrules[i]))
		# cmc_syncrules: add a syncrule for the 'accept' action. all but process i must synchronise on it
		newvect = []
		for j in range(0,len(network.procs)+1):
			if j != i:
				newvect.append(ACCEPT)
			else:
				newvect.append('*')
		if i == 0:
			cmc_syncrules[i][1][ACCEPT] = [(newvect, ACCEPT)]
		else:
			cmc_syncrules[i][0][ACCEPT] = [(newvect, ACCEPT)]
		# cmc_constraintsconstr_syncrules: add a syncrule for the 'accept' action. all processes must synchronise on it
		cmc_constraintsconstr_syncrules[i][0][ACCEPT] = [([ACCEPT for j in range(0,len(network.procs)+1)], ACCEPT)]
		# create suitable syncactions entry for these syncrules
		copy_syncactions = copy.deepcopy(network.syncactions)
		# extend by one for constraints LTS
		copy_syncactions.append(set([]))
		# add "accept" to each position except i
		for j in range(0,len(network.procs)):
			if j != i:
				copy_syncactions[j] |= {ACCEPT}
		copy_syncactions[i] = network.procsactprefixsets[i]
		copy_syncactions[len(copy_syncactions)-1] = network.procsactprefixsets[i] | {ACCEPT}
		cmc_syncactions.append(copy_syncactions)
		# cmc_constraintsconstr_syncactions:
		copy_syncactions2 = copy.deepcopy(copy_syncactions)
		copy_syncactions2[i] |= {ACCEPT}
		cmc_constraintsconstr_syncactions.append(copy_syncactions2)
	# add one additional entry in procsactsets for constraints LTS
	network.procsactsets.append(set([]))

def cmc_preprocess_property():
	"""preprocess the property LTS using the given network"""

	# processes for check network
	checkprocs = []
	checkheaders = []

	# insert abstracted w.r.t. property and minimised versions of the processes
	for i in range(0,len(network.procs)-1):
		cmc_createHidden_LTS(i, {len(network.procs) - 1}, "")
		cmc_weaktrace_minimise_LTS(network.procfiles[i][:-4] + "_hidden")
		[h,v,a] = aut.read(network.folder, network.procfiles[i][:-4] + "_hidden_wtmin.aut")
		checkprocs.append(v)
		checkheaders.append(h)
	# insert property in check
	checkprocs.append(network.procs[len(network.procs)-1])
	checkheaders.append(network.procsheaders[len(network.procs)-1])

	# iterate over the processes and update the property LTS
	for i in range(0,len(network.procs)-1):
		if os.path.isfile(os.path.join(network.folder, "ref_prop.aut")):
			os.remove(os.path.join(network.folder, "ref_prop.aut"))
		if os.path.isfile(os.path.join(network.folder, "ref_prop_min.aut")):
			os.remove(os.path.join(network.folder, "ref_prop_min.aut"))
		generateLTS(checkheaders, checkprocs, network.procsactsets, network.syncrules, network.syncactions, os.path.join(network.folder, "ref_prop" + str(i)), opt.quiet, config.outputobject, 0, [i, len(checkprocs)-1], 0, False, True, False)
		[h,v,a] = aut.read(network.folder, "ref_prop" + str(i) + ".aut")
		# prune parts that cannot reach accepting states
		(h2,v2) = cmc_prune_LTS(h, v)
		aut.write(network.folder, h2, v2, "ref_prop_pruned" + str(i))
		cmc_weaktrace_minimise_LTS("ref_prop_pruned" + str(i))
		[h,v,a] = aut.read(network.folder, "ref_prop_pruned" + str(i) + "_wtmin.aut")
		# update property LTS
		checkprocs[len(network.procs)-1] = v
		checkheaders[len(network.procs)-1] = h
	# update property to final outcome
	if os.path.isfile(os.path.join(network.folder, "ref_property.aut")):
		os.remove(os.path.join(network.folder, "ref_property.aut"))
	os.rename(os.path.join(network.folder, "ref_prop_pruned" + str(i) + "_wtmin.aut"), os.path.join(network.folder, "ref_property.aut"))
	network.procfiles[len(network.procs)-1] = "ref_property.aut"

def cmc_check():
	"""apply compositional model checking to verify LTS network"""
	global nontrivialpropactions, prop_priority, procfiles, procsheaders, procs, syncrules, syncactions, procsactprefixsets, procsactsets, constraintsLTSs, constraintsLTStree, constraintsLTSs, basic_constraintsLTSs, propertyLTSs, cmc_syncrules, cmc_syncactions, cmc_constraintsconstr_syncrules, cmc_constraintsconstr_syncactions, cmc_constraintsdep, cmc_checktree, cmc_checklist, cmc_constraints_updates, checkprocs, checkheaders, abstractcheckprocs, abstractcheckheaders, constraintsupdateprocs, constraintsupdateheaders, constraintsLTS_is_extended, nrchecksshift
	
	# variables used to keep track of memory statistics
	max_states_in_check = 0
	states_in_check = 0
	# count the number of checks performed globally and per process since the last shift
	nrchecks = 0
	#nrchecksshift = [0 for j in range(0,len(network.procs)-1)]
	nrchecksshift = 0
	#
	#last position in the configuration at which a rotation was performed
	last_rotation_pos = -1
	# direction in which the verification is moving
	direction_forward = True
	# are the constraints LTSs extended?
	constraintsLTS_is_extended = [False for j in range(0,len(network.procs)-1)]
	
	# bound on number of checks before a global shift is performed
	shiftbound = 10000
# 	# bound on semi-composition update
# 	semibound = 20
# 	# semicounts per process
# 	updatecount = [0 for j in range(0,len(network.procs)-1)]
	
	# we use a list of process ids
	cmc_checklist = []
	# processes for check network
	checkprocs = []
	checkheaders = []
	# abstract versions of processes
	abstractcheckprocs = []
	abstractcheckheaders = []
	# network to update constraints
	constraintsupdateprocs = []
	constraintsupdateheaders = []
	# tree to keep track of constraintsLTSs for different check configurations
	#cmc_checktree = ({},set([]))
	# constraints dependency function: on which current position in check does the constraints LTS of process i depend?
	cmc_constraintsdep = [-1 for i in range(0,len(network.procs)-1)]

	# construct constraintsLTSs and property LTSs
	basic_constraintsLTSs = []
	propertyLTSs = []
	# create constraints LTS tree
	constraintsLTStree = [[(),[]] for i in range(len(network.procs)-1)]
	#constraintsLTS_is_extended = []
	#cmc_constraints_updates = []
	for i in range(0,len(network.procs)-1):
		# for every process, we maintain up to len(network.procs)-1 constraint LTSs
		#constraintsLTSs.append(['*' for j in range(0,len(network.procs)-1)])
		basic_constraintsLTSs.append(())
		propertyLTSs.append(())
		cmc_createInitialConstraintsLTS(i)
		#constraintsLTS_is_extended.append(False)
		#cmc_constraints_updates.append((len(network.procs),len(network.procs)))
	# local references to the constraintsLTSs in the tree
	constraintsLTSs = [() for i in range(len(network.procs)-1)]

	# based on property dependencies, fix an initial check order for processes
	previous_syncactions = nontrivialpropactions
	#print(prop_dependency)
	if cmc_checklist == []:
		for i in range(0,len(prop_dependency)):
			propclass = list(prop_dependency[i])
			#propclass.sort(key=lambda x: int(procsheaders[x][2]))
			#propclass.sort(key=lambda x : (len(procsactsets[x] & previous_syncactions)/int(procsheaders[x][2]), int(procsheaders[x][2])), reverse=True)
			propclass = deque(propclass)
			current_syncactions = set([])
			while len(propclass) > 0:
				p = propclass.popleft()
				cmc_checklist.append(p)
				checkprocs.append({})
				checkheaders.append(['0','0','0'])
				abstractcheckprocs.append({})
				abstractcheckheaders.append(['0','0','0'])
				constraintsupdateprocs.append({})
				constraintsupdateheaders.append(['0','0','0'])
				current_syncactions |= procsactsets[p]
			previous_syncactions = current_syncactions
	#cmc_checklist = [0,4,1,5,2,6,3,7,8,9]
	# two extra procs and headers for property LTS and constraints LTS
	checkprocs.append({})
	checkheaders.append(['0','0','0'])
	checkprocs.append({})
	checkheaders.append(['0','0','0'])
	abstractcheckprocs.append({})
	abstractcheckheaders.append(['0','0','0'])
	abstractcheckprocs.append({})
	abstractcheckheaders.append(['0','0','0'])

	constraintsupdateprocs.append({})
	constraintsupdateheaders.append(['0','0','0'])
	constraintsupdateprocs.append({})
	constraintsupdateheaders.append(['0','0','0'])

	# the numbers of accepting states to search for at every step of the check
	#cmc_accnumber = [10,5,1]
	cmc_accnumber = [1 for i in range(0,len(procs)+1)]

	# index of currently considered position in cmc_checklist
	check_current = 0
	while check_current < len(cmc_checklist):
	#while check_current < 1:
		i = cmc_checklist[check_current]
		if nrchecksshift == shiftbound:
			# move all processes from position check_current one step to the right in cmc_checklist. move final process to check_current in cmc_checklist
			# forget current abstracted, minimised version of the property LTS for the involved processes
			# store the constraints LTS of the current first process as its new initial constraints LTS and
			# reset the constraints LTS of the new first process to its initial LTS
			rotateConfiguration(0, len(cmc_checklist)-1)
			#updatecount = [0 for j in range(0,len(cmc_checklist))]
			last_rotation_pos = 0
			nrchecksshift = 0
			check_current = 0
			direction_forward = True

# 			for j in range(check_current,len(cmc_checklist)):
# 				propertyLTSs[cmc_checklist[j]] = ()
# 			# store constraints LTS of current first process as its new initial constraints LTS
# 			#initial_constraintsLTSs[cmc_checklist[0]] = copy.deepcopy(constraintsLTSs[cmc_checklist[0]][0])
# 			# move
# 			j = len(cmc_checklist)-2
# 			# create new configuration first
# 			cmc_checklist_new = copy.deepcopy(cmc_checklist)
# 			tmp = cmc_checklist_new[len(cmc_checklist)-1]
# 			while j >= check_current:
# 				cmc_checklist_new[j+1] = cmc_checklist_new[j]
# 				j -= 1
# 			cmc_checklist_new[check_current] = tmp
# 			# turn
# 			j = len(cmc_checklist)-2
# 			while j >= check_current:
# 				checkprocs[cmc_checklist[j]] = {'0': {ACCEPT: set(['0'])}}
# 				checkheaders[cmc_checklist[j]] = ['0','1','1']
# 				# move constraints LTS?
# 				if constraintsLTS_is_extended[cmc_checklist[j]]:
# 					if not existsConstraintsLTS(j+1, cmc_checklist_new):
# 						insertSingleConstraintsLTS(copy.deepcopy(getConstraintsLTS(j)), j+1, cmc_checklist_new)
# 				# else remove constraints LTS in old position
# 				else:
# 					removeConstraintsLTSs(j)
# 				if existsConstraintsLTS(j+1, cmc_checklist_new):
# 					constraintsLTS_is_extended[cmc_checklist[j]] = True
# 				# reset shift counter
# 				nrchecksshift[j+1] = 0
# 				j -= 1
# 			checkprocs[cmc_checklist_new[check_current]] = {'0': {ACCEPT: set(['0'])}}
# 			checkheaders[cmc_checklist_new[check_current]] = ['0','1','1']
# 			cmc_checklist = cmc_checklist_new
# 			# reset shift counter
# 			nrchecksshift[check_current] = 0
# 			# update extended flag
# 			if check_current == 0:
# 				constraintsLTS_is_extended[cmc_checklist[check_current]] = False
# 			elif existsConstraintsLTS(check_current, cmc_checklist_new):
# 				constraintsLTS_is_extended[cmc_checklist[check_current]] = True
			# reset constraints LTS of new first process to its initial LTS
			#constraintsLTSs[cmc_checklist[0]] = copy.deepcopy(initial_constraintsLTSs[cmc_checklist[0]])
# 		elif updatecount[check_current] == semibound:
# 			print_message('adding complete process')
# 			# insert complete proc to compute full semi-composition with next process
# 			checkprocs[i] = network.procs[i]
# 			checkheaders[i] = network.procsheaders[i]
# 			constraintsLTSs[i] = getConstraintsLTS(check_current)
# 			check_current += 1
		else:
			# new check
			nrchecks += 1
			#nrchecksshift[check_current] += 1
			#nrchecksshift += 1
			#print(nrchecks)
			# possibly update constraints LTSs
			#cmc_update_constraints_LTSs(check_current)
			# retrieve constraints LTS
			# keep track of number of states in check
			# create check network for this process, and perform the check
			# add current process and its constraints LTS to the network

			constraintsLTSs[i] = getConstraintsLTS(check_current)
			# if this is not the first check in the sequence, we first check against an abstract version of the next component
			if check_current > 0 and direction_forward:
				if abstractcheckprocs[i] == {}:
					# create abstract checkproc
					proclist = cmc_checklist[:check_current] + [len(procs)-1]
					cmc_createHidden_LTS(i, set(proclist), "")
					cmc_weaktrace_minimise_LTS(procfiles[i][:-4] + "_hidden")
					[h,v,a] = aut.read(network.folder, procfiles[i][:-4] + "_hidden_wtmin.aut")
					abstractcheckprocs[i] = v
					abstractcheckheaders[i] = h
				checkprocs[i] = abstractcheckprocs[i]
				checkheaders[i] = abstractcheckheaders[i]

				states_in_check += int(basic_constraintsLTSs[i][0][2])
			
				checkprocs[len(procs)] = basic_constraintsLTSs[i][1]
				checkheaders[len(procs)] = basic_constraintsLTSs[i][0]
			else:
				checkprocs[i] = procs[i]
				checkheaders[i] = procsheaders[i]
				
				states_in_check += int(constraintsLTSs[i][0][2])
				
				checkprocs[len(procs)] = constraintsLTSs[i][1]
				checkheaders[len(procs)] = constraintsLTSs[i][0]
#			printstr = str(nrchecksshift) + ", " + str(updatecount) + ": "
			printstr = str(nrchecksshift) + ": "
			if i == cmc_checklist[0]:
				printstr += "[*" + str(cmc_checklist[0]) + "*"
			else:
				printstr += "[" + str(cmc_checklist[0])
			for k in range(1,len(cmc_checklist)):
				if i == cmc_checklist[k]:
					printstr += ",*" + str(cmc_checklist[k]) + "*"
				else:
					printstr += "," + str(cmc_checklist[k])
			print(printstr + "]: " + checkheaders[len(network.procs)][2] + ", " + checkheaders[len(network.procs)][1])
			# add property LTS
			cmc_checklist_insert_abstract_property_LTS(check_current)
			# debug output
# 			for k1 in range(0,len(network.procs)-1):
# 				print("process " + str(k1) + ":")
# 				for k2 in range(0,int(checkheaders[k1][2])):
# 					outgoing = checkprocs[k1].get(str(k2),{})
# 					print(str(k2) + ": " + str(outgoing))
# 			print("syncrules: " + str(cmc_syncrules[i]))
# 			print("syncactions: " + str(cmc_syncactions[i]))
			genresult = generateLTS(checkheaders, checkprocs, procsactsets, cmc_syncrules[i], cmc_syncactions[i], os.path.join(network.folder, "check"), opt.quiet, config.outputobject, 0, cmc_checklist[:check_current+1] + [len(procs)-1,len(procs)], cmc_accnumber[check_current], True, True, False)
			# for monitoring reasons: read size of generated LTS
			inFile = open(os.path.join(network.folder, "check.aut"), 'r')
			# scan the first line
			line = inFile.readline()
			global token, next
			results, remainder = aut.scanner.scan(line)
			inFile.close()
			# read the header
			# an aut file has three values in the header
			news = int(results[3][1])
			#newt = int(results[2][1])
			if (states_in_check+news) > max_states_in_check:
				max_states_in_check = states_in_check+news
			# first, if there is no counter-example, read the feedback, and determine if there are only false negative actions, making
			# the produced constraint invalid.
			if genresult and check_current > 0:
				# construct constraint
				isrealconstraint = cmc_createConstraint(check_current-1)
				if isrealconstraint:
					[h,v,a] = aut.read(network.folder, "constraint_tmin.aut")
					prevconstraint = [h,v]
				else:
					genresult = False
			# is there a counter-example? if so, read it
			if not genresult and check_current > 0:
				# perform another check, now with the concrete check LTS
				checkprocs[i] = procs[i]
				checkheaders[i] = procsheaders[i]
				states_in_check -= int(basic_constraintsLTSs[i][0][2])
				states_in_check += int(constraintsLTSs[i][0][2])

				checkprocs[len(procs)] = constraintsLTSs[i][1]
				checkheaders[len(procs)] = constraintsLTSs[i][0]

				genresult = generateLTS(checkheaders, checkprocs, procsactsets, cmc_syncrules[i], cmc_syncactions[i], os.path.join(network.folder, "check"), opt.quiet, config.outputobject, 0, cmc_checklist[:check_current+1] + [len(procs)-1,len(procs)], cmc_accnumber[check_current], True, True, False)
				# for monitoring reasons: read size of generated LTS
				inFile = open(os.path.join(network.folder, "check.aut"), 'r')
				# scan the first line
				line = inFile.readline()
				global token, next
				results, remainder = aut.scanner.scan(line)
				inFile.close()
				# read the header
				# an aut file has three values in the header
				news = int(results[3][1])
				#newt = int(results[2][1])
				if (states_in_check+news) > max_states_in_check:
					max_states_in_check = states_in_check+news
				if genresult and check_current > 0:
					# construct constraint
					isrealconstraint = cmc_createConstraint(check_current-1)
					if isrealconstraint:
						[h,v,a] = aut.read(network.folder, "constraint_tmin.aut")
						prevconstraint = [h,v]
					else:
						genresult = False
			if not genresult:
				direction_forward = True
				# first, if there is also a semi-composition, take it into account
				# NOT ALLOWED, since from incomplete searches, constraints cannot be derived
				# alternative is to always completely explore the state spaces
# 				if os.path.isfile(os.path.join(network.folder, "check_semicomp.aut")):
# 					# read semi-composition
# 					[h,v,a] = aut.read(network.folder, "check_semicomp.aut")
# 					# replace check LTS of prev_pos with the semi-composition
# 					checkprocs[prev_pos] = v # !TODO: relabel ACCEPT_NOSYNC to ACCEPT
# 					checkheaders[prev_pos] = h
# 					# extend constraints LTS of prev_pos
# 					cmc_extendConstraintsLTS(cmc_checklist[prev_pos], prev_pos, (h,v), False)
# 					constraintsLTS_is_extended[cmc_checklist[prev_pos]] = True
# 					# delete all constraintsLTSs depending on process to be updated
# 					removeConstraintsLTSs(0, [cmc_checklist[prev_pos]])
# 					os.remove(os.path.join(network.folder, "check_semicomp.aut"))
				# read counter-example
				[h,v,actions] = cmc_createCounterexample_LTS()
				# determinise the LTS
				detLTS = [[],{}]
				determiniseLTS([h,v], detLTS)
				# place this counter-example in check network, and move forward in checking
				checkprocs[i] = detLTS[1]
				checkheaders[i] = detLTS[0]
				
				# determine which process to check next, based on the last counter-example trace
				if check_current+1 < len(cmc_checklist):
					directacts = readCounterexampleActions()
					#bestmatchnumber = 0
					bestmatch = -1
					#bestprio = 100
					bestsize = -1
					for nextproc in range(check_current+1,len(cmc_checklist)):
						intersect = procsactsets[cmc_checklist[nextproc]] & directacts
						# in case two LTSs are equally suitable as a next process, we only choose a new one over another in case a significant difference in size is there (nr. of states)
						#if len(intersect) > bestmatchnumber or (len(intersect) == bestmatchnumber and (bestnrstates == -1 or int(procsheaders[cmc_checklist[nextproc]][2]) < bestnrstates/2)):
						if prop_priority.get(cmc_checklist[nextproc],100) == prop_priority.get(cmc_checklist[check_current]):
							#prop_priority.get(cmc_checklist[nextproc],100) <= bestprio
							if len(intersect) > 0 and (bestsize == -1 or int(procsheaders[cmc_checklist[nextproc]][2]) < bestsize):
								bestsize = int(procsheaders[cmc_checklist[nextproc]][2])
								#bestmatchnumber = len(intersect)
								bestmatch = nextproc
					# have we found a suitable proc? if not, check for entire action set
					if bestmatch == -1:
						#bestmatchnumber = 0
						for nextproc in range(check_current+1,len(cmc_checklist)):
							intersect = procsactsets[cmc_checklist[nextproc]] & actions
							#if len(intersect) > bestmatchnumber or (len(intersect) == bestmatchnumber and (bestnrstates == -1 or int(procsheaders[cmc_checklist[nextproc]][2]) < bestnrstates/2)):
							if prop_priority.get(cmc_checklist[nextproc],100) == prop_priority.get(cmc_checklist[check_current]):
								if len(intersect) > 0 and (bestsize == -1 or int(procsheaders[cmc_checklist[nextproc]][2]) < bestsize):
									bestsize = int(procsheaders[cmc_checklist[nextproc]][2])
									#bestmatchnumber = len(intersect)
									bestmatch = nextproc
						# finally, just take the next process if still no process was selected
						if bestmatch == -1:
							for nextproc in range(check_current+1,len(cmc_checklist)):
								if prop_priority.get(cmc_checklist[nextproc],100) == prop_priority.get(cmc_checklist[check_current]):
									bestmatch = nextproc
							if bestmatch == -1:
								bestmatch = check_current+1
					nextproc = bestmatch
					# now rotate to ensure the next process is the one selected
					rotateConfiguration(check_current+1, nextproc)
					last_rotation_pos = check_current+1
				check_current += 1
				#print(newtrans)
			# no counter-example. if we are looking at the first process, we have established that no counter-example exists at all.
			# otherwise, backtrack to previous process
			else:
				if check_current == 0:
					break
				else:
					direction_forward = False
					#identify the process with lowest configuration position at which a counter-example with current process cannot be constructed
					prev_pos = check_current-1
					if check_current > last_rotation_pos:
						for j in range(0,check_current-1):
							# perform check. checking for a single accepting state now suffices
							genresult = generateLTS(checkheaders, checkprocs, procsactsets, cmc_syncrules[i], cmc_syncactions[i], os.path.join(network.folder, "check"), opt.quiet, config.outputobject, 0, cmc_checklist[:j+1] + [cmc_checklist[check_current]] + [len(procs)-1,len(procs)], 1, True, True, False)
							# for monitoring reasons: read size of generated LTS
							inFile = open(os.path.join(network.folder, "check.aut"), 'r')
							# scan the first line
							line = inFile.readline()
							global token, next
							results, remainder = aut.scanner.scan(line)
							inFile.close()
							# read the header
							# an aut file has three values in the header
							news = int(results[3][1])
							if (states_in_check+news) > max_states_in_check:
								max_states_in_check = states_in_check+news
							# is there no counter-example? then record last findings and break out of the loop
							if genresult:
								# construct constraint
								isrealconstraint = cmc_createConstraint(prev_pos)
								if isrealconstraint:
									[h,v,a] = aut.read(network.folder, "constraint_tmin.aut")
									prevconstraint = [h,v]
									# remember current checked position
									prev_pos = j
									break
					# prev_pos now points to the process that needs altered constraints.
					# determinise the LTS
					newconstraint = [[],{}]
					determiniseLTS(prevconstraint, newconstraint)
					# update constraints LTS of prev_pos
					states_in_check -= int(constraintsLTSs[cmc_checklist[prev_pos]][0][2])
					cmc_extendConstraintsLTS(cmc_checklist[prev_pos], prev_pos, newconstraint, False)
					constraintsLTS_is_extended[cmc_checklist[prev_pos]] = True
					# delete all constraintsLTSs depending on updated constraintsLTS
					removeConstraintsLTSs(prev_pos, cmc_checklist)
					# one more check: should the initial constraints LTS of prev_pos also be altered?
					if prev_pos > 0:
						print("performing extra check to update initial constraints")
						genresult = generateLTS(checkheaders, checkprocs, procsactsets, cmc_syncrules[i], cmc_syncactions[i], os.path.join(network.folder, "check"), opt.quiet, config.outputobject, 0, [cmc_checklist[prev_pos], cmc_checklist[check_current]] + [len(procs)-1,len(procs)], 1, True, True, False)
						# for monitoring reasons: read size of generated LTS
						inFile = open(os.path.join(network.folder, "check.aut"), 'r')
						# scan the first line
						line = inFile.readline()
						global token, next
						results, remainder = aut.scanner.scan(line)
						inFile.close()
						# read the header
						# an aut file has three values in the header
						news = int(results[3][1])
						if (states_in_check+news) > max_states_in_check:
							max_states_in_check = states_in_check+news
						# was no accepting state reached? then record findings
						if genresult:
							# construct constraint
							cmc_createConstraint(prev_pos)
							[h,v,a] = aut.read(network.folder, "constraint_tmin.aut")
							# determinise the LTS
							newconstraint = [[],{}]
							determiniseLTS([h,v], newconstraint)
							# update initial constraints LTS of prev_pos
							cmc_extendConstraintsLTS(cmc_checklist[prev_pos], prev_pos, newconstraint, True)
							# delete all constraintsLTSs depending on process to be updated
							removeConstraintsLTSs(0, [cmc_checklist[prev_pos]])
					# move back. while doing so, reset visited checkprocs and constraints lTSs
					tmp = check_current
					while tmp > prev_pos:
						# update number of states in check						
						states_in_check -= int(constraintsLTSs[cmc_checklist[tmp]][0][2])
						# clear LTS from check
						#checkheaders[cmc_checklist[tmp]] = ['0','0','0']
						#checkprocs[cmc_checklist[tmp]] = {}
						#abstractcheckheaders[cmc_checklist[tmp]] = ['0','0','0']
						#abstractcheckprocs[cmc_checklist[tmp]] = {}
						# reset shift counter
						#nrchecksshift[tmp] = 0
						# go to previous position
						tmp -= 1

					#print("Update: " + str(prev_pos) + " " + str(t[0]) + " " + str(t[1]))
# # 					print("Current proc header: " + str(checkheaders[cmc_checklist[prev_pos]]))
# # 					print("Current proc: " + str(checkprocs[cmc_checklist[prev_pos]]))
# 					print("Cur: " + str(constraintsLTSs[cmc_checklist[prev_pos]][0]))
# 					constr_tmp = copy.deepcopy(constraintsLTSs[cmc_checklist[prev_pos]])
# 					print("New: " + str(constraintsLTSs[cmc_checklist[prev_pos]][0]))
# 					if constraintsLTSs[cmc_checklist[prev_pos]][0][1] == constr_tmp[0][1] and constraintsLTSs[cmc_checklist[prev_pos]][0][2] == constr_tmp[0][2]:
# 						print("Current proc header: " + str(checkheaders[cmc_checklist[prev_pos]]))
# 						print("Current proc: " + str(checkprocs[cmc_checklist[prev_pos]]))
# 						aut.write(network.folder, constr_tmp[0], constr_tmp[1], "constr-old")
# 						aut.write(network.folder, constraintsLTSs[cmc_checklist[prev_pos]][0], constraintsLTSs[cmc_checklist[prev_pos]][1], "constr-new")
# 						exit(1)
					# rotate configuration such that check_current is situated at prev_pos+1

					rotateConfiguration(prev_pos+1, check_current)

					#updatecount = [0 for j in range(0,len(cmc_checklist))]
					#for tmp in range(prev_pos+1, len(cmc_checklist)):
					#	updatecount[tmp] = 0
					# record this rotation
					
					last_rotation_pos = prev_pos+1
# 					
					#if prev_pos == check_current-1:
# 						updatecount[prev_pos] += 1
					# increment nrchecksshift
					#if t[1] == 'True':
					nrchecksshift += 1

					check_current = prev_pos
					#states_in_check -= int(min_constraintsLTSs[cmc_checklist[prev_pos]][0][2])

	# report
	if check_current == 0:
		print_message('Network satisfies property!')
	else:
		print_message('Network does NOT satisfy property!')
		# for i in range(0,len(network.procs)-1):
		# 	print("process " + str(i) + ":")
		# 	for j in range(0,int(checkheaders[i][2])):
		# 		outgoing = checkprocs[i].get(str(j),{})
		# 		print(str(j) + ": " + str(outgoing))
	print_message('Largest number of states in a check: ' + str(max_states_in_check))
	print_message('Number of checks performed: ' + str(nrchecks))
	# remove constraints files on disk
	for fl in glob.glob(os.path.join(network.folder, "cons_*")):
		os.remove(fl)
	for fl in glob.glob(os.path.join(network.folder, "check*")):
		os.remove(fl)
	for fl in glob.glob(os.path.join(network.folder, "constraint*")):
		os.remove(fl)
	for fl in glob.glob(os.path.join(network.folder, "*hidden*")):
		os.remove(fl)
	return check_current == 0

# --- the main functions for verification / transformation ---

def refiner_readRulesystem():
	print_message('reading rule system ' + config.rs_name)
	print_separator()
	readRulesystem(os.path.join(config.rs_folder, config.rs_name))
	print_message('finished reading rule system ' + config.rs_name)
	print_message('---')

def refiner_constructhidingset():
	# derive the action hiding set from a property
	global hideactions
	if config.property_name == "":
		hideactions = ['none']
	else:
		hideactions = []
		print_message('constructing hiding set')
		print_separator()
		constructHidingSet()
		print_message('finished reading property ' + config.property_name)
		print_message('---')

def refiner_generateLTS():
	print_message('generating system LTS')
	if opt.genbound > 0:
		print_message('generation bound is ' + str(opt.genbound))
	if opt.safety_onthefly:
		print_message('checking safety property on-the-fly')
	print_separator()
	if opt.safety_onthefly:
		genresult = generateLTS(procsheaders, procs, [], syncrules, syncactions, os.path.join(network.folder, network.name), opt.quiet, config.outputobject, opt.genbound, list(range(0,len(procsheaders))), 1, False, False, opt.log_generate)
		if not genresult:
			print_message('Property violated!')
		else:
			print_message('Property satisfied!')
	else:
		generateLTS(procsheaders, procs, [], syncrules, syncactions, os.path.join(network.folder, network.name), opt.quiet, config.outputobject, opt.genbound, list(range(0,len(procsheaders))), 0, False, True, opt.log_generate)
	inFile = open(os.path.join(network.folder, network.name + ".aut"), 'r')
	# read the header
	line = inFile.readline()
	global token, next
	results, remainder = aut.scanner.scan(line)
	inFile.close()
	print_message('generated ' + results[3][1] + ' states and ' + results[2][1] + ' transitions')

def refiner_preparedivinfo():
	# check if the sets of process nondiverging states is already available on disk
	global revhashtable, procsheaders, procs, syncrules, syncactions
	opt.divergency = True
	if not os.path.isfile(os.path.join(network.folder, network.name + "_" + config.property_name + ".ndv")):
		# check if the network is present on disk.
		if not os.path.isfile(os.path.join(network.folder, network.name + ".aut")):
			print_message("system .aut file does not exist, it will be generated!")
			print_separator()
			print_message('generating system LTS')
			print_separator()
			generateLTS(network.procsheaders, network.procs, [], network.syncrules, network.syncactions, os.path.join(network.folder, network.name), opt.quiet, config.outputobject, opt.genbound, list(range(0,len(network.procsheaders))), 0, False, True, False)
		print_separator()
		print_message("reading system LTS")
		print_separator()
		[systemLTSheader, systemtrans, systemactset] = aut.read(network.folder, network.name + ".aut")
		print_message("reading state mapping")
		print_separator()
		revhashtable = readMap(network.folder, network.name)
		if not hideactions:
			print_message('reading hiding set')
			print_separator()
			try:
				inFile = open(os.path.join(config.property_folder, config.property_name + ".hs"), 'r')
				readHideActions(inFile)
				inFile.close()
			except IOError:
				print_error("action hiding file does not exist!")
		# compute the set of tau-diverging states
		print_message('computing set of tau-diverging system states')
		divergencyset = computeDivergencySet(systemLTSheader, systemtrans)
		print_separator()
		print_message('computing the non-diverging process states')
		computeNonDivergingProcessStates()
		print_separator()
		print_message('writing non-diverging process states to disk')
		writeProcndivsets(network.name, config.property_name)
		print_separator()

def refiner_transform(div):
	global transformed_procs_new_states, transformed_procs, transformed_procsheaders
	transformed_procs_new_states = []
	transformed_procs = []
	transformed_procsheaders = []
	opt.divergency = div
	if opt.divergency:
		refiner_preparedivinfo()
	preprocessRulesystem()
	print_message('checking confluence of rule system ' + config.rs_name)
	print_separator()
	checkConfluence()
	# check if divergency info needs to be updated when transforming
	if config.property_name != "":
		try:
			inFile = open(os.path.join(network.folder, network.name + "_" + config.property_name + ".ndv"), 'r')
		except IOError:
			opt.divergency = False
			inFile = 0
		if inFile != 0:
			opt.divergency = True
	else:
		opt.divergency = False
	if opt.divergency:
		print_message('reading non-diverging process states list')
		print_separator()
		readProcndivsets(network.name, config.property_name)
	print_message('determining matches of rules in ' + config.rs_name + ' on process LTSs of ' + network.name)
	print_separator()
	matchRulesystem()
	print_separator()
	print_message('checking applicability of synchronisation rules of ' + config.rs_name + ' on those of ' + network.name)
	print_separator()
	matchSyncrules()
	print_message('refining the process LTSs of ' + network.name)
	print_separator()
	transform()
	print_separator()
	if opt.divergency:
		print_message('updating the lists of non-diverging states of ' + network.name)
		print_separator()
		updateNonDivergingProcessStates()
		print_message('writing updated non-diverging process states')
		print_separator()
		writeNewProcndivsets(network.name, config.property_name)
	print_message('writing the new network')
	print_separator()
	expopen_syncacts = newsyncactions if opt.expopenoutput else None
	network.write(network.folder, transformed_procs, transformed_procsheaders, network.procfiles, newsyncrules, network.name, expopen_syncacts)
	print_message('TRANSFORMATION FINISHED: network ' + network.name + ' has been transformed and saved as network ' + config.transformed_network_name)
	print_message('---')
	# transformed network becomes new input network
	network.read(config.transformed_network_name)

def refiner_verify(div, fair):
	opt.divergency = div
	opt.fairness = fair
	if opt.divergency:
		refiner_preparedivinfo()
	preprocessRulesystem()
	print_message('checking confluence of rule system ' + config.rs_name)
	print_separator()
	checkConfluence()
	if opt.divergency:
		print_message('reading non-diverging process states list of ' + network.name)
		print_separator()
		readProcndivsets(network.name, config.property_name)
		print_message('determining matches of rules of ' + config.rs_name + ' on process LTSs of ' + network.name)
		print_separator()
		matchRulesystem()
		print_separator()
		print_message('checking applicability of synchronisation rules of ' + config.rs_name)
		print_separator()
		matchSyncrules()
	print_message('constructing preservation checks for rule system ' + config.rs_name)
	print_separator()
	starttimer = time.time()
	constructChecks()
	if not hideactions:
		print_message('reading hiding set')
		print_separator()
		try:
			inFile = open(os.path.join(config.property_folder, config.property_name + ".hs"), 'r')
			readHideActions(inFile)
			inFile.close()
		except IOError:
			print_error("action hiding file does not exist!")
	if config.property_name == '':
		config.property_name = 'semantics'
	if not opt.newcheck:
		print_message('checking preservation of ' + config.property_name + ' for ' + config.rs_name)
		print_separator()
		checkPropPreservation()
	else:
		print_message('checking preservation of ' + config.property_name + ' for ' + config.rs_name + ' with the new version of the check')
		print_separator()
		checkPropPreservationNew()
	endtimer = time.time()
	outFile = open(os.path.join(network.folder, "refiner_runtime"), 'w')
	outFile.write(str(endtimer - starttimer))
	outFile.close()

# IMPORTANT: for compositional mc, we currently assume that the network is structured in such a way, that for all actions a,
# a process can only fire a if all other processes that have a in their alphabet can also fire a in the current state.
# Support for other networks is future work.
def refiner_compositional_mc():
	global prop_dependency, cmc_checklist
	# first we partition the process LTSs based on their dependency w.r.t. the property (final LTS in the network)
	print_message('determining dependency of process LTSs on property')
	print_separator()
	cmc_constructDependency()
	print_message('preparing data structures')
	print_separator()
	cmc_construct_network_structures()
	#print_message('preprocessing property')
	#cmc_preprocess_property()
	print_message('checking')
	cmc_check()

# --- END main functions

def main(args):
	"""The main function"""
	global hideactions
	displayed_help = False
	for i in range(0,len(args)):
		if args[i] == '-h':
			displayed_help = True
			print("Usage: pypy/python3 refiner.py [-gprcdfeqtCn]") #TODO: [-gprcdfeqtCn] needs to be updated
			print("")
			print("Refine a given network of LTSs according to a given rule system,")
			print("or analyse either such a network or such a rule system")
			print("")
			print(" -g                    generate the LTS of the given network")
			print(" -l                    write a log file to disk containing a list of state indices in the order they were visited during LTS generation")
			print(" -o                    generate the LTS, and check on-the-fly safety property included in network")
			print(" -p <prop>             determine property preservation of mu-calculus formula <prop>.mcl")
			print(" -r <rule system>      refine a given network according to rule system <rule system>.rs")
			print(" -c <rule system>      check property preservation for <rule system>.rs. Select a property with -p")
			print(" -c2                   Flag to indicate that the new version of property preservation checking should be used (replaces '-c')")
			print(" -d                    take divergency in processes into account")
			print(" -f                    check property preservation under fairness (all divergency is ignored)")
			print(" -e                    when refining, write resulting network in exp.open form (i.e. add one-party sync. rules)")
			print(" -q                    quiet mode, no messages to screen")
			print(" -t <n>                use n threads in parallel for property preservation checking")
			print(" -icc                  apply compositional model checking with Incremental Counter-Example Construction (assumes presence of a property LTS)")
			print(" -n <network>          the input network <network>.exp")
			print(" -b <bound>            perform a bounded search (state space generation)")
			print(" -m <plugin>           load and use the plugin module <plugin>.py (e.g. 'plugins.my_plugin', combine with -h to display plugin usage instructions")
			print(" -mdir <dir>           loads the plugin modules in the folder <dir>, combine with -h to display usage instructions of the loaded plugins")
			# display plugin help
			for plugin in loaded_plugins:
				print("")
				print("Plugin: "+plugin.__name__)
				plugin.printHelp()
		elif args[i] == '-p':
			i += 1
			opt.prop = args[i]
		elif args[i] == '-g':
			opt.generate = True
		elif args[i] == '-l':
			opt.log_generate = True
		elif args[i] == '-o':
			opt.safety_onthefly = True
		elif args[i] == '-r':
			i += 1
			opt.transform = args[i]
		elif args[i] == '-c':
			i += 1
			opt.check = args[i]
		elif args[i] == '-c2':
			opt.newcheck = True
		elif args[i] == '-d':
			opt.divergency = True
		elif args[i] == '-f':
			opt.fairness = True
		elif args[i] == '-e':
			opt.expopenoutput = True
		elif args[i] == '-q':
			opt.quiet = True
		elif args[i] == '-t':
			i += 1
			config.nrthreads = int(args[i])
		elif args[i] == '-icc':
			i += 1
			opt.compositional_mc = True
		elif args[i] == '-n':
			i += 1
			opt.network = args[i]
		elif args[i] == '-b':
			i += 1
			opt.genbound = int(args[i])
		elif args[i] == '-m':
			i += 1
			loaded_plugins.append(plugin_loader.loadPlugin(args[i]))
		elif args[i] == '-mdir':
			i += 1
			loaded_plugins.extend(plugin_loader.loadPluginsFromFolder(args[i]))

	# If help was displayed, do not do anything else
	if (displayed_help):
		return

	# initialize plugins
	for plugin in loaded_plugins:
		plugin.init(args)

	# check that we have all required input
	if opt.generate or opt.transform != "" or opt.divergency or opt.compositional_mc:
		if opt.network == "":
			print_error("no network specified!")
	if opt.check != "":
		if opt.prop == "":
			#print_error("no property specified!")
			hideactions = ['none']
	if opt.compositional_mc and (opt.generate or opt.transform or opt.divergency or opt.check):
		print_error("combination of options is invalid!")

	if opt.network != "":
		network.readFromPath(opt.network)

	if opt.generate or opt.safety_onthefly:
		# generate the LTS of the given network
		refiner_generateLTS()

	if opt.prop:
		config.property_folder, config.property_name = os.path.split(opt.prop)
		if not os.path.isfile(os.path.join(config.property_folder, config.property_name + ".hs")):
				opt.constructhidingset = True

	if opt.constructhidingset:
		refiner_constructhidingset()

	if opt.transform != "":
		config.rs_folder, config.rs_name = os.path.split(opt.transform)
		refiner_readRulesystem()
		refiner_transform(opt.divergency)

	if opt.check != "":
		config.rs_folder, config.rs_name = os.path.split(opt.check)
		refiner_readRulesystem()
		refiner_verify(opt.divergency, opt.fairness)

	if opt.compositional_mc:
		refiner_compositional_mc()

	# run plugins
	for plugin in loaded_plugins:
		plugin.run()

if __name__ == '__main__':
	args = []
	for i in range(1,len(sys.argv)):
		args.append(sys.argv[i])
	main(args)

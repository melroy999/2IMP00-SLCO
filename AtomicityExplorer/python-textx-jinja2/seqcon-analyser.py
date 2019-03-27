import sys
from os import mkdir
from os.path import exists, dirname, basename, join, split
from copy import deepcopy
import itertools
import glob
from enum import Enum
import re, traceback

this_folder = dirname(__file__)

# import libraries
sys.path.append(join(this_folder,'../../libraries'))
from slcolib import *
from SCCTarjan import identifySCCs_lower_bound

class MemoryModel(Enum):
	TSO = 1
	PSO = 2
	ARM = 3

# Characteristics of memory model
RW_order = True
WR_order = True
RR_order = True
WW_order = True

memory_model = MemoryModel.TSO
model_statespace = {}
modelname = ""
model = []
DG = {}
DG_P = {}
DG_C = {}

# dictionary providing info on conflicting accesses between instructions due to speculative reading
DG_C_spec_conflicts = {}

# structures providing info on the structure of the SLCO model
instructions_objects = {}
instructions_IDs = {}
instructions_accesses = {}
SMowner = {}

# structures for Johnson's algorithm
blocked = {}
B = {}

#structure containing the cycles
critical_cycles = {}

autscanner=re.Scanner([
  (r"des",															lambda scanner,token:("HEADER", token)),
  (r"[0-9]+",														lambda scanner,token:("NAT", token)),
  (r"[\s\(\),]+", None), # None == skip token.
  (r"[A-Za-z0-9!\_\-?.\*\']+\([A-Za-z0-9!\_\-?,.\*\'\(\)\[\]]+\)|[A-Za-z0-9!\_\-?.\*\'\[\]]+|[\"\'][A-Za-z0-9!?\_\-\#\s.,\*\'\(\)\[\]]+[\"\']",	lambda scanner,token:("ACTION", token)),
])

rwscanner=re.Scanner([
  (r"rw\(", None),
  (r"[\"\s\(\),]+", None), # None == skip token.
  (r"[A-Za-z0-9!\_\-?.\*\'\(\)]+", lambda scanner,token:("NAME", token)),
  (r"ST\'[0-9]+", lambda scanner,token:("STID", token)),
  (r"\[", lambda scanner,token:("BEGINLIST", token)),
  (r"\]", lambda scanner,token:("ENDLIST", token)),
])

def peek(stack):
	"""Return but do not pop top element of stack"""
	return stack[len(stack) - 1]

def unblock(u):
	"""Procedure for Johnson's algorithm"""
	global blocked, B

	blocked[u] = False
	Bu = B.get(u, set([]))
	for w in Bu:
		if blocked[w]:
			unblock(w)
	B[u] = set([])

def circuit(L, s, o):
	"""Procedure for Johnson's algorithm"""
	global blocked, B, critical_cycles, instructions_accesses, SMowner

	# Set of visited threads in cycle detection
	T = set([])
	current_thread = SMowner[instructions_accesses[s][1]]

	# call stack
	callstack = []
	outgoing = L.get(s, set([]))
	callstack.append((s, list(outgoing), False))
	blocked[s] = True
	while callstack != []:
		v, targets, f = peek(callstack)
		move_to_next = False
		while len(targets) > 0:
			w = targets.pop()
			if w == s and T != set([]):
				# put stack in list of critical cycles (at least two threads are involved)
				trace = []
				for n, tgt, f2 in callstack:
					trace.append(n)
				print("adding " + str(trace) + " to list of critical cycles")
				critlist = critical_cycles.get(o.name, [])
				critlist.append(trace)
				critical_cycles[o.name] = critlist
				callstack[len(callstack)-1] = (v, targets, True)
			elif not blocked[w]:
				# condition for criticality (thread visitation)
				w_thread = SMowner[instructions_accesses[w][1]]
				if w_thread not in T:
					if w_thread != current_thread:
						T.add(current_thread)
						current_thread = w_thread
					# put w on the callstack
					woutgoing = L.get(w, set([]))
					callstack.append((w, list(woutgoing), False))
					blocked[w] = True
					move_to_next = True
					break
		if not move_to_next:
			if f:
				unblock(v)
			else:
				# put v in B sets of successors
				for w in L.get(v, set([])):
					Bw = B.get(w, set([]))
					Bw.add(v)
					B[w] = Bw
			callstack.pop()
			# update predecessor
			if f:
				if len(callstack) > 0:
					n, tgt, f2 = peek(callstack)
					callstack[len(callstack)-1] = (n, tgt, f)

def detect_critical_cycles():
	"""Detect conflict cycles in given graph. Based on Johnson's algorithm for the detection of elementary circuits"""
	# list of all states
	global blocked, B, DG_P, DG_C, T, model, instructions_accesses, SMowner

	for o in model.objects:
		# Conbine the C and P relations
		DG = deepcopy(DG_P[o.name])
		for i, tgts in DG_C[o.name].items():
			p_tgts = DG.get(i, set([]))
			p_tgts |= DG_C[o.name][i]
			DG[i] = p_tgts

		states = set(DG.keys())
		for s in DG.keys():
			states |= DG[s]
		max_state = max(states)

		for s in states:
			blocked[s] = False

		# additional structures to keep track of blocking status of states
		s = 0
		while s < max_state+1:
			# compute subgraph of DG induced by {s, ..., n}
			SCCs = list()
			identifySCCs_lower_bound(DG, {}, SCCs, s)
			# Detect SCC with minimal vertex number
			scc_index = 0
			minimal_vertex = max_state+1
			for i in range(0, len(SCCs)):
				nodes = (SCCs[i][1].keys())
				nodes.sort()
				if nodes[0] < minimal_vertex and SCCs[i][1][nodes[0]] != set([]):
					scc_index = i
					minimal_vertex = nodes[0]
			if minimal_vertex < max_state+1:
				s = minimal_vertex
				for t in SCCs[scc_index][1].keys():
					blocked[t] = False
					B[t] = set([])
				circuit(SCCs[scc_index][1], s, o)
				s += 1
			else:
				s = max_state+1

def postprocess_critical_cycles():
	"""Postprocess detected cycles to identify fence insertion suggestions"""
	global critical_cycles, DG_P, DG_C, instructions_accesses

	for o_name in critical_cycles.keys():
		for C in critical_cycles[o_name]:
			print(C)
			# Summarise and compress the P-traces
			C_summary = []
			P_trace_accesses = {}
			# store conditional reads, reads, and writes of each P trace
			exploring_P_trace = False
			P_trace_start = 0
			for i in range(0, len(C)):
				s = C[i]
				t = C[(i+1)%len(C)]
				if t in DG_P[o_name].get(s, set([])):
					if not exploring_P_trace:
						exploring_P_trace = True
						P_trace_start = s
						P_trace_summary = (set([]), set([]), set([]))
					else:
						if t != P_trace_start:
							ap = instructions_accesses[s][2]
							if ap[0][1] == set([]):
								condreads = ap[0][0]
								api = 1
							else:
								condreads = set([])
								api = 0
							reads = set([])
							writes = set([])
							while api < len(ap):
								reads |= ap[api][0] - writes - condreads
								writes |= ap[api][1]
								api += 1
							P_trace_summary = (P_trace_summary[0]|condreads, P_trace_summary[1]|reads, P_trace_summary[2]|writes)
						else:
							C_summary.append([P_trace_start,P_trace_start])
							P_trace_accesses[P_trace_start] = P_trace_summary
				else:
					if exploring_P_trace:
						exploring_P_trace = False
						C_summary.append([P_trace_start,s])
						P_trace_accesses[P_trace_start] = P_trace_summary
					else:
						C_summary.append([s])
			print(C_summary)
			print(P_trace_accesses)

def readAut(autfile):
	"""Read a .aut file and place the data in a dictionary"""
	trans = {}

	try:
		inFile = open(autfile,'r')
	except IOError:
		print_error(".aut file of SLCO model does not exist!")
		return {}
	# scan the first line
	line = inFile.readline()
	global token, next
	results, remainder = autscanner.scan(line)
	inFile.close()

	# read the header
	if results[0][0] != 'HEADER':
		print_error("unexpected start of .aut description!")
	transheader = []
	# an aut file has three values in the header
	for index in range(1,4):
		transheader.append(results[index][1])

	# count to remove double entries
	ntrans = 0
	actset = set([])

	#store transitions in memory
	currentsrc = ''
	newentry = {}
	first = True
	for transline in open(autfile):
		tl, remainder = autscanner.scan(transline)
		src = tl[0][1]
		act = tl[1][1]
		tgt = tl[2][1]
		if not first:
			# add quotes if not present
			act.replace('\'', '"')
			if act[0] != '"':
				act = '"' + act + '"'
			# put transition label in actset
			actset.add(act)
			# are we building a new dictionary entry?
			if src != currentsrc:
				# possibly add old entry if not empty
				if currentsrc != '':
					trans[currentsrc] = newentry
				currentsrc = src
				newentry = {}
			outgoingwithlabel = newentry.get(act)
			if outgoingwithlabel == None:
				newentry[act] = set([tgt])
				ntrans += 1
			else:
				if tgt not in outgoingwithlabel:
					# insert new element
					outgoingwithlabel.add(tgt)
					newentry[act] = outgoingwithlabel
					ntrans += 1
		else:
			first = False
	# add final entry
	trans[currentsrc] = newentry
	transheader[1] = str(ntrans)
	return [transheader, trans, actset]

def read_statespace(m):
	"""Read the state space of the model"""
	global model_statespace

	statespace_name = m[:-4] + "aut"
	model_statespace = readAut(statespace_name)

def preprocess():
	global instructions_objects, SMowner, model
	# construct list of instruction names with pointers to the objects
	instructions_objects = {}
	for c in model.classes:
		for sm in c.statemachines:
			for tr in sm.transitions:
				instructions_objects["ST'" + str(tr._tx_position)] = tr.statements[0]
	# construct function providing for given statement the owning SM
	SMowner = {}
	for c in model.classes:
		for sm in c.statemachines:
			for tr in sm.transitions:
				SMowner["ST'" + str(tr._tx_position)] = sm

def get_smallest_accesses(id):
	global instructions_accesses
	"""Return the set of smallest accesses of the given instruction (indicated by number) id"""
	instr = instructions_accesses[id]

	if len(instr[2]) > 0:
		if instr[2][0][0] != set([]) and instr[2][0][1] == set([]):
			return instr[2][0]
	rset = set([])
	wset = set([])
	writes = set([])
	for i in range(0,len(instr[2])):
		ap = instr[2][i]
		rset |= (ap[0] - writes)
		if ap[0] == set([]):
			wset |= ap[1]
		writes |= ap[1]
	return tuple([rset, wset])

def get_largest_accesses(id):
	global instructions_accesses
	"""Return the set of largest accesses of the given instruction (indicated by number) id"""
	instr = instructions_accesses[id]

	if len(instr[2]) == 1 and instr[2][0][1] == set([]):
		return instr[2][0]
	else:
		wset = set([])
		for i in range(0, len(instr[2])):
			wset |= instr[2][i][1]
		return tuple([set([]),wset])

def instructions_are_conflicting(i1, i2):
	"""Return whether the first instruction conflicts with the second"""
	global instructions_accesses

	reads = set([])
	writes = set([])
	for p in instructions_accesses[i1][2]:
		reads |= p[0]
		writes |= p[1]
	return accesspattern_conflicts_with_instruction(tuple([reads, writes]), i2)

def accesspattern_conflicts_with_instruction(ap, i1):
	"""Return whether the given access pattern ap conflicts with the instruction i1"""
	global instructions_accesses

	reads = ap[0]
	writes = ap[1]
	conflicting = False
	for a in reads:
		c1 = conflicting_accesses(a, False, i1)
		if c1[0] != set([]) or c1[1] != set([]):
			return True
	for a in writes:
		c1 = conflicting_accesses(a, True, i1)
		if c1[0] != set([]) or c1[1] != set([]):
			return True
	return False

def instructions_are_parallel(a1, a2):
	"""Return whether the two instructions can possibly be executed in parallel (are from different statemachines of the same object)"""
	global instructions_accesses, SMowner

	if a1 == '\"tau\"' or a2 == '\"tau\"':
		return True
	ac1 = instructions_accesses[a1]
	ac2 = instructions_accesses[a2]
	if ac1[0] == ac2[0]:
		return SMowner[ac1[1]] != SMowner[ac2[1]]
	else:
		return False

def conflicting_accesses(a, iswrite, ins):
	global instructions_accesses
	"""For the given access a, provide the accesses of instruction ins conflicting with a. Boolean iswrite indicates whether a is a write or not"""
	ap = instructions_accesses[ins][2]
	# merge reads and writes
	readsap = set([])
	writesap = set([])
	for p in ap:
		readsap |= p[0]
		writesap |= p[1]
	conflicting = tuple([set([]), set([])])
	if iswrite:
		if a in readsap:
			conflicting[0].add(a)
	if a in writesap:
		conflicting[1].add(a)
	return conflicting

def constructDG():
	"""Construct the dependency graph of the SLCO model"""
	global model, model_statespace, DG_P, DG_C, DG_C_spec_conflicts, instructions_objects, instructions_IDs, instructions_accesses, memory_model, SMowner, RR_order

	# construct dictionary of instruction IDs
	L = list(model_statespace[2])
	instructions_IDs = {}
	j = 0
	for i in range(0,len(L)):
		if L[i] != '\"tau\"':
			instructions_IDs[L[i]] = j
			j += 1

	# construct dictionary of accesses for the instructions
	instructions_accesses = {}
	for a in model_statespace[2]:
		if a != '\"tau\"':
			rw, remainder = rwscanner.scan(a)
			i = 4
			reads = set([])
			writes = set([])
			read = False
			accessmode = False
			alist = []
			while i < len(rw):
				if rw[i][0] == 'BEGINLIST':
					accessmode = True
					if not read:
						reads = set([])
					else:
						writes = set([])
					i += 1
				elif rw[i][0] == 'ENDLIST':
					if accessmode:
						if not read:
							read = True
						else:
							alist.append(tuple([reads, writes]))
							accessmode = False
					else:
						break
					i += 1
				elif rw[i][1] == 'A\'(':
					i += 1
				else:
					if not read:
						reads.add(rw[i][1])
					else:
						writes.add(rw[i][1])
					i += 1
			instructions_accesses[instructions_IDs[a]] = tuple([rw[0][1], rw[2][1], alist])

	# Build dependency graph - P-relation
	DG_P = {}
	for o in model.objects:
		DG_P[o.name] = {}
	# construct P-relation. Iterate over all states, consider their outgoing transitions, and compare these to the outgoing transitions of successors.
	for i in range(0, int(model_statespace[0][2])):
		s = str(i)
		outgoing = model_statespace[1].get(s,{})
		s_aset = set(outgoing.keys())
		for a, tgts in outgoing.items():
			if a != '\"tau\"':
				j = instructions_IDs[a]
				for t in tgts:
					t_outgoing = model_statespace[1].get(t,{})
					t_aset = set(t_outgoing.keys())
					enabled = t_aset - s_aset
					tgtset = set([])
					for a2 in enabled - set(['\"tau\"']):
						tgtset.add(instructions_IDs[a2])
					out = DG_P[instructions_accesses[j][0]].get(j,set([]))
					DG_P[instructions_accesses[j][0]][j] = out | tgtset

	# Build dependency graph - C-relation
	DG_C = {}
	for o in model.objects:
		DG_C[o.name] = {}
	# construct C-relation. Iterate over all states, consider their outgoing transitions, and compare those from different state machines w.r.t. conflicting accesses.
	parallel_instructions = {}
	for i in range(0, int(model_statespace[0][2])):
		s = str(i)
		outgoing = model_statespace[1].get(s,{})
		s_aset = set(outgoing.keys()) - set(['\"tau\"'])
		for a in s_aset:
			aid = instructions_IDs[a]
			paset = set([])
			for a2 in s_aset:
				a2id = instructions_IDs[a2]
				if instructions_are_parallel(aid, a2id):
					paset.add(a2id)
			par = parallel_instructions.get(aid,set([]))
			parallel_instructions[aid] = par | paset
	for aid in parallel_instructions.keys():
		for aid2 in parallel_instructions[aid]:
			if instructions_are_conflicting(aid, aid2):
				# Not yet present in P-relation?
				if aid2 not in DG_P[instructions_accesses[aid][0]].get(aid,set([])) and aid not in DG_P[instructions_accesses[aid2][0]].get(aid2,set([])):
					out = DG_C[instructions_accesses[aid][0]].get(aid,set([]))
					out.add(aid2)
					DG_C[instructions_accesses[aid][0]][aid] = out
	
	# For each guarded statement, obtain the predecessors in P, to identify C conflicts with that guarded statement if execution of those predecessors does not
	# enable the guarded statement
	predecessors = {}
	for i in range(0, len(instructions_IDs)):
		a = instructions_accesses[i]
		if a[2][0][0] != set([]) and a[2][0][1] == set([]):
			preddict = predecessors.get(instructions_accesses[i][0], {})
			preddict[i] = set([])
			predecessors[instructions_accesses[i][0]] = preddict
			for j in range(0, len(instructions_IDs)):
				if i in DG_P[instructions_accesses[i][0]].get(j,set([])) and SMowner[instructions_accesses[i][1]] == SMowner[instructions_accesses[j][1]]:
					predecessors[instructions_accesses[i][0]][i].add(j)

	# For each guarded statement, add conflicts with the statements executed in parallel with the former's predecessors
	#for o in model.objects:
	#	for 

	# Perform a DFS from each guarded statement to identify reads that can be done speculatively. Only relevant if speculative reading is allowed by the memory model
	speculative_reads = {}
	if not RR_order:
		for o in model.objects:
			speculative_reads[o.name] = {}
			for i in predecessors[o.name].keys():
				ap = instructions_accesses[i][2]
				condreads_i = ap[0][0]
				specreads = {}
				blocked = set([])
				# first check speculative reads for i itself
				if len(ap) > 1:
					reads = set([])
					writes = set([])
					accesses = set([])
					for pi in range(1,len(ap)):
						reads |= (ap[pi][0] - writes - condreads_i)
						writes |= ap[pi][1]
					for a in condreads | reads:
						if a not in blocked and a not in condreads_i:
							accesses.add(a)
							if a in condreads:
								blocked.add(a)
					blocked |= writes 
					specreads[i] = accesses
				# call stack for DFS
				callstack = []
				onstack = set([])
				blocked_vars = {}
				outgoing = DG_P[o.name].get(i, set([]))
				# put instruction on call stack. Third argument is the set of variables that are blocked from speculative reading
				# (due to having observed a write to those variables on the stack trace)
				callstack.append((i, list(outgoing), blocked))
				onstack.add(i)
				while callstack != []:
					j, tgts, blocked = peek(callstack)
					# stop early if WR is guaranteed
					if WR_order:
						if blocked != set([]):
							callstack.pop()
							continue
					while len(tgts) > 0:
						k = peek(tgts)
						if not k in onstack and (blocked_vars.get(k) == None or not (blocked_vars.get(k, set([])) <= blocked)):
							# - any variables read from by k, not yet written to along the trace, and not read from by i can be done speculatively
							# - any variables written to by k should be blocked from speculative reading further down the trace. If WR is guaranteed
							# by the memory model, further searching is actually not needed.
							ap = instructions_accesses[k][2]
							if ap[0][1] == set([]):
								condreads = ap[0][0]
								pi = 1
							else:
								condreads = set([])
								pi = 0
							reads = set([])
							writes = set([])
							while pi < len(ap):
								reads |= (ap[pi][0] - writes - condreads)
								writes |= ap[pi][1]
								pi += 1

							kblocked = deepcopy(blocked)
							for a in condreads | reads:
								if a not in blocked and a not in condreads_i:
									accesses = specreads.get(j,set([]))
									accesses.add(a)
									specreads[j] = accesses
									if a in condreads:
										kblocked.add(a)
							kblocked |= writes

							# put k on call stack
							koutgoing = DG_P[o.name].get(k, set([]))
							callstack.append((k, list(koutgoing), kblocked))
							onstack.add(k)
							break
						else:
							tgts.pop()
					if len(tgts) == 0:
						# close j
						B = blocked_vars.get(j, set([]))
						blocked_vars[j] = (B & blocked)
						# pop j off call stack
						callstack.pop()
						onstack.remove(j)
				speculative_reads[o.name][i] = specreads
			print(speculative_reads[o.name])

	print("C relation without spec reads: " + str(DG_C))
	print(" ")
	# add additional C-edges to handle guarded statements
	for o in model.objects:
		for i in predecessors[o.name].keys():
			condreads_i = instructions_accesses[i][2][0][0]
			# construct list of parallel instructions
			parallel_instr = set([])
			for j in predecessors[o.name][i]:
				parallel_instr |= parallel_instructions.get(j, set([]))
			# check for conflicts, and if present, add a C-edge
			for j in parallel_instr:
				if accesspattern_conflicts_with_instruction(tuple([condreads,set([])]), j):
					if i not in DG_P[o.name].get(j, set([])) and j not in DG_P[o.name].get(i, set([])):
						out = DG_C[o.name].get(i, set([]))
						out.add(j)
						DG_C[o.name][i] = out
						out = DG_C[o.name].get(j, set([]))
						out.add(i)
						DG_C[o.name][j] = out
				# Take speculative reading into account?
				if not RR_order:
					spreads = speculative_reads[o.name][i]
					for k, accs in spreads.items():
						if k not in parallel_instructions.get(j, set([])):
							conflicting_reads_k = set([])
							conflicting_accesses_j = tuple([set([]), set([])])
							for a in accs:
								accesses = conflicting_accesses(a, False, j)
								if accesses != tuple([set([]),set([])]):
									if j not in DG_P[o.name].get(k, set([])) and k not in DG_P[o.name].get(j, set([])):
										out = DG_C[o.name].get(j, set([]))
										out.add(k)
										DG_C[o.name][j] = out
										out = DG_C[o.name].get(k, set([]))
										out.add(j)
										DG_C[o.name][k] = out
										conflicting_accesses_j[0] |= accesses[0]
										conflicting_accesses_j[1] |= accesses[1]
										conflicting_reads_k.add(a)
							# record access conflicts between j and k
							conflicts = DG_C_spec_conflicts.get(j, {})
							conflicts[k] = conflicting_accesses_j
							DG_C_spec_conflicts[j] = conflicts
							conflicts = DG_C_spec_conflicts.get(k, {})
							conflicts[j] = tuple([conflicting_reads_k, set([])])
							DG_C_spec_conflicts[k] = conflicts
	print("C-relation with spec reads: " + str(DG_C))

def main(args):
	"""The main function"""
	global modelname, model, memory_model, model_statespace, RW_order, RW_order, RR_order, WW_order, critical_cycles
	if len(args) == 0:
		print("Missing arguments: SLCO model")
		sys.exit(1)
	else:
		if args[0] == '-h' or args[0] == '-help':
			print("Usage: pypy/python3 slco2mcrl2")
			print("")
			print("Check given SLCO model for sequentially inconsistent behaviour. For the model, a .aut file containing its state space is required.")
			print(" -w                                    weak memory model to consider (TSO,PSO,ARM) (default: TSO)")
			sys.exit(0)
		else:
			i = 0
			while i < len(args):
				if args[i] == '-w':
					if args[i+1] == "PSO":
						memory_model = MemoryModel.PSO
						WR_order = False
						RW_order = True
						RR_order = True
						WW_order = False
						print("memory model set to PSO")
					elif args[i+1] == "ARM":
						memory_model = MemoryModel.ARM
						WR_order = False
						RW_order = False
						RR_order = False
						WW_order = False
						print("memory model set to ARM")
					else:
						memory_model = MemoryModel.TSO
						WR_order = False
						RW_order = True
						RR_order = True
						WW_order = True				
						print("memory model set to TSO")
					i += 1
				else:
					modelname = args[i]
				i += 1

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
		model = read_SLCO_model(file)
		try:
			print("extracting relevant info from the SLCO model")
			preprocess()
			# read state space
			print("reading the state space of the SLCO model")
			read_statespace(modelname)
			print("constructing dependency graph")
			constructDG()
			print("detecting critical cycles in dependency graph")
			detect_critical_cycles()
			print("postprocessing cycles")
			postprocess_critical_cycles()
		except Exception:
			print("failed to process model %s" % basename(file))
			print(traceback.format_exc())

if __name__ == '__main__':
	args = []
	for i in range(1,len(sys.argv)):
		args.append(sys.argv[i])
	main(args)

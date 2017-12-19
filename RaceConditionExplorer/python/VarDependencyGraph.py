from lts.SCCTarjan import identifySCCs
from utils import stack


class VarDependencyGraph:
	dependency_graph = dict()
	_locked = set()
	
	# Expects a list consisting of tuples of the form (act, state_machine_id, set(read_vars), set(write_vars))
	def __init__(self, rw_list, locked = set()):
		# build dictionary mapping write variables to actions
		write_dict = dict()
		for a, sm_id, _, write_vars in rw_list:
			for w in write_vars:
				action_set = write_dict.get(w, set())
				action_set.add((a, sm_id))  # a race condition can only occur if different state machines access the variable
				write_dict[w] = action_set
		# build dependency graph for rw_list
		for i in range(0,len(rw_list)):
			src, sm_id, read_vars, write_vars = rw_list[i]
			
			# a race condition may occur when two transitions both write to more than one common variable
			# if |write_vars[i] cap write_vars[j]| > 1 then write_vars[i] cap write_vars[j] must be locked
			if len(write_vars) > 1:
				for j in range(i+1,len(rw_list)):
					_, _, _ , write_vars2 = rw_list[j]
					w_intersect = write_vars & write_vars2
					if len(w_intersect) > 1:
						locked |= w_intersect
					
			# build dependency graph
			outgoing = self.dependency_graph.get(src, {})
			for r in read_vars:
				if r in locked:
					continue
				targets = write_dict.get(r, set())
				# a race condition may occur when a transitions writes and reads a variable and another transition writes as well
				# if read_vars cap write_vars cap write_vars_of_other_transition is not empty, then add result to locked
				if r in write_vars and len(targets) > 1:
					locked.add(r)
					continue
				# for each action 'tgt', add 'r' to the labels of transition src --labels--> tgt
				for tgt, tgt_sm_id in targets:
					# a race condition can only occur if different state machines access the variable,
					# if read/write is done to by the same state machine the behaviour follows the specification
					# described by the model and is intended
					if sm_id != tgt_sm_id:
						labels = outgoing.get(tgt, set())  # we use tgt as key since labels sets are updated and not hashable
						labels.add(r)
						outgoing[tgt] = labels
			if outgoing:
				self.dependency_graph[src] = outgoing
		self._locked = locked

		
	def get_locked_sets(self):
		locked_sets = set()
		for outgoing in self.dependency_graph.values():
			for labels in outgoing.values():
				if len(labels) > 1:
					locked_sets.add(frozenset(labels))
		return locked_sets
					
	def get_locked(self, locked):
		locked |= self._locked
		self.remove_locked_labels_from_transitions(locked)
		self.add_scc_locks(locked)
		return locked
		
	def remove_locked_labels_from_transitions(self, locked):
		if not locked:
			return
		for outgoing in self.dependency_graph.values():
			for k in list(outgoing.keys()): # copy keys since we're deleting
				outgoing[k] -= locked # remove labels that are locked
				if not outgoing[k]: #if transition labels is empty, remove the transition
					del outgoing[k]
		# remove source states without transitions
		for src in list(self.dependency_graph.keys()):
			if not self.dependency_graph[src]:
				del self.dependency_graph[src]
	
	def add_scc_locks(self, locked):
		# convert dependency graph format for Tarjan's SCC algorithm
		SCCs = list()
		identifySCCs(self.dependency_graph, dict(), SCCs)
		for scc in SCCs:
			if scc[0] <= 1:
				continue
			_depth_first_break_cycles(scc[1], locked)
		
	def find_cycles(self):
		#TODO: Geert: implement Johnson
		cycles = list()
		for src, outgoing in self.dependency_graph.items():
			for tgt, labels in outgoing.items():
				print("Transition from %s to %s with the the set(!) of labels %s" % (src, tgt, labels))
		return cycles


# @post: finds back-edges and removes all labels on this back-edge from other transitions
# @param: graph         the graph
# @param: back_labels   a set of labels that will be ignored as edges and to labels that are
#                       removed from the graph are added
def _depth_first_break_cycles(graph, back_labels):
	visited = set()
	for s in list(graph.keys()):
		if s in visited:
			continue
		
		state_stack = stack()
		labels_stack = stack()
		state_stack.append(s)
		labels_stack.append({s}) # a dummy label set, to pop at the end of the first loop
		while state_stack:
			labels = labels_stack.peek()
			state = state_stack.peek()
			if labels <= back_labels or state in visited:
				# edge was removed in a previous iteration
				# or state was already visited
				state_stack.pop()
				labels_stack.pop()
				continue
				
			visited.add(state)
			outgoing = graph.get(state, {})
			for tgt, labels in list(outgoing.items()):
				if tgt not in visited:
					state_stack.append(tgt)
					labels_stack.append(labels)
				elif tgt in state_stack:
					# if tgt is visited and in state_stack, then there is a cycle!
					back_labels |= labels
					for var in list(labels):
						_remove_transitions_with_var(graph, var)
			
		

# @post: var has been removed from all transitions;
#        if this results in a transition with no labels, the transition is removed
def _remove_transitions_with_var(dependency_graph, var):
	for outgoing in dependency_graph.values():
		for k in list(outgoing.keys()): # copy keys since we're deleting
			outgoing[k].discard(var)
			if not outgoing[k]: #if transition labels is empty, remove the transition
				del outgoing[k]

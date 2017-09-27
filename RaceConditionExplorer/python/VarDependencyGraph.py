from lts.SCCTarjan import identifySCCs
from utils import stack


class VarDependencyGraph:
	dependency_graph = dict()
	
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
		for src, sm_id, read_vars, _ in rw_list:
			outgoing = dict()
			for r in read_vars:
				if r in locked:
					continue
				# for each action 'tgt', add 'r' to the labels of transition src --labels--> tgt
				targets = write_dict.get(r, set())
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
		# cleanup empty transitions
		self.remove_locked_labels_from_transitions(locked)
		
	def get_locked_sets(self):
		locked_sets = set()
		for outgoing in self.dependency_graph.values():
			for labels in outgoing.values():
				if len(labels) > 1:
					locked_sets.add(frozenset(labels))
		return locked_sets
					
	def get_locked(self, locked):
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
		visited = {}
		for s in list(self.dependency_graph.keys()):
			if s in visited:
				continue
			
			state_stack = stack()
			state_stack.append((None, s, None))
			while state_stack:
				src, state, label = state_stack.peek()
				if state in visited:
					# state was already visited
					state_stack.pop()
					if src:
						# add transition
						state_labels = visited[src].get(state, set())
						state_labels.add(frozenset(label))
						visited[src][state] = state_labels
						# add shortcut transitions
						for tgt, sets in visited[state].items():
							tgt_labels = visited[src].get(tgt, set())
							tgt_labels |= {frozenset(labels | label) for labels in sets}
							visited[src][tgt] = tgt_labels
					continue
				
				visited[state] = {}
				outgoing = self.dependency_graph.get(state, {})
				for tgt, labels in list(outgoing.items()):
					# continue DFS
					state_stack.append((state, tgt, labels))
		# the variables involved in cycles are now the label sets on self loops
		cycles = set()
		for src, outgoing in visited.items():
			self_loops = outgoing.get(src)
			if self_loops:
				cycles |= self_loops
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

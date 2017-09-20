from lts.SCCTarjan import identifySCCs

class VarDependencyGraph:
	locked = set()
	locked_sets = set()
	dependency_graph = dict()
	
	# Expects a list consisting of tuples of the form (act, set(read_vars), set(write_vars))
	def __init__(self, rw_list):
		# build dictionary mapping write variables to actions
		write_dict = dict()
		for a, _, write_vars in rw_list:
			for w in write_vars:
				action_set = write_dict.get(w, set())
				action_set.add(a)
				write_dict[w] = action_set
		# build dependecy graph for rw_list
		for src, read_vars, _ in rw_list:
			outgoing = dict()
			for r in read_vars:
				if r in self.locked:
					continue
				# for each action 'tgt', add 'r' to the labels of transition src --labels--> tgt
				targets = write_dict[r]
				for tgt in targets:
					labels = outgoing.get(tgt, set()) # we use tgt as key since labels sets are not hashable and updated
					labels.add(r)
					outgoing[tgt] = labels
			if outgoing:
				self.dependency_graph[src] = outgoing
	
	def calculate_locks(self):
		for outgoing in self.dependency_graph.values():
			for labels in outgoing.values():
				if len(labels) > 1:
					self.locked |= labels
					self.locked_sets.add(labels)
		self.remove_locked_labels_from_transitions()
		self.add_scc_locks()
		return self.locked, self.locked_sets
		
	def remove_locked_labels_from_transitions(self):
		for outgoing in self.dependency_graph.values():
			for k in list(outgoing.keys()): # copy keys since we're deleting
				outgoing[k] -= self.locked # remove labels that are locked
				if not outgoing[k]: #if transition labels is empty, remove the transition
					del outgoing[k]
		# remove source states without transitions
		for src in list(self.dependency_graph.keys()):
			if not self.dependency_graph[src]:
				del self.dependency_graph[src]
	
	
	def add_scc_locks(self):
		# convert dependency graph format for Tarjan's SCC algorithm
		L = self.dependency_graph
		SCCdict = dict()
		SCCs = list()
		identifySCCs(L, SCCdict, SCCs)
		b_locked_updated = False
		for the_scc in SCCs:
			scc_decomp = [the_scc]
			while scc_decomp:
				scc = scc_decomp.pop()
				if scc[0] <= 1:
					continue
				
				if not b_locked_updated:
					rem_label = None
					for src, outgoing in scc[1].items():
						if outgoing:
							labels = iter(outgoing.values()).next()
							rem_label = labels.pop()
							# NOTE: the hope is that by removing rem_label, the cycle(s) are broken
							# TODO: Would it make sense to remove the smallest set entirely such that the cycle is guaranteed to be broken?
							self.locked.add(rem_label)
							b_locked_updated = True
							break
					_remove_transitions_with_var(scc[1], rem_label)
				
				newSCCs = list()
				identifySCCs(scc[1], dict(), newSCCs)
				scc_decomp.extend(newSCCs)
				
				

def _remove_transitions_with_var(dependency_graph, var):
	for outgoing in dependency_graph.values():
		for k in list(outgoing.keys()): # copy keys since we're deleting
			outgoing[k].discard(var)
			if not outgoing[k]: #if transition labels is empty, remove the transition
				del outgoing[k]

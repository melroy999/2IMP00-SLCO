
from transformation_utils import *
from utils import stack

STATEMENT_MEMORY_FENCE = '#'

def parse_var(var):
	return var.split("'")[1]
	

def parse_suggestions(sugg_path):
	file = open(sugg_path, 'r')
	lines = file.readlines()
	file.close()

	suggestions = {}
	for line in lines:
		start = line.find(",") + 2
		end = line.rfind("'") - 1
		line = line[start:end]
		sm, line = get_and_remove_up_to_first(line, ',', 2)
		statement, line = get_and_remove_up_to_first(line, ',', 2)
		statement = int(statement[3:])

		if line.startswith('AD'):
			ad = suggestions.get(statement, AD(set(), set()))
			ad.merge(AD.parse(line))
			suggestions[statement] = ad

	for ad in suggestions.values():
		ad.fix_conflicting_shuffles()
	total = 0
	for ad in suggestions.values():
		total += ad.size()
	print total
	return suggestions


class SuggestionSyntaxException(Exception):
	def __init__(self, value):
		self.parameter = value

	def __str__(self):
		return repr(self.parameter)


class AccessPattern:
	r = set()
	w = set()

	def __init__(self, r, w):
		self.r = r
		self.w = w

	def __hash__(self):
		return hash((frozenset(self.r), frozenset(self.w)))

	@staticmethod
	def parse(text):
		text = text[3:-1]
		splt = text.split('], [')
		rtxt = splt[0][1:]
		wtxt = splt[1][:-1]
		rset = {x.split("'")[1] for x in rtxt.split(', ')} if rtxt else set()
		wset = {x.split("'")[1] for x in wtxt.split(', ')} if wtxt else set()
		return AccessPattern(rset, wset)

	def find_assignment_full(self, statement_list, start):
		for i in range(start, len(statement_list)):
			statement = statement_list[i]
			if statement.__class__.__name__ == "str":
				continue
			b_write_found = len(self.w) == 0 or (len(self.w) == 1 and statement.left.var.name in self.w)
			reads = set()
			get_read_vars_from_expression(statement.right, reads)
			b_reads_found = not (self.r - reads)  # reads found if result is empty set
			# return if required elements are found
			if b_write_found and b_reads_found:
				return i
		return -1

	def satisfies_partially(self, statement):
		write = None
		expression = None
		reads_found = set()
		if statement.__class__.__name__ == "Assignment":
			if self.w:
				if statement.left.var.name in self.w:
					write = statement.left.var.name

			expression = statement.right
		elif statement.__class__.__name__ == "Expression":
			expression = statement

		if expression:
			get_read_vars_from_expression(expression, reads_found)
			reads_found = reads_found & self.r  # set of reads found
		return write, reads_found

	def find_sub_composite(self, composite):
		# -2 indicates not found, -1 indicates guard partially satisfies pattern
		first = -2
		last = -2

		_, reads = self.satisfies_partially(composite.guard)
		if reads:
			last = first = -1

		total_writes = set()
		total_reads = set()

		for i in range(0, len(composite.assignments)):
			write, reads = self.satisfies_partially(composite.assignments[i])
			if write or reads:
				if write:
					total_writes.add(write)
				total_reads = total_reads | reads
				if first == -2:
					last = first = i
				else:
					last = i

		# return_statements = [composite]
		# when self.r and self.w are fully covered then we have a sub composite
		read_remainder = (self.r - total_reads)
		write_remainder = (self.w - total_writes)
		# if remainders are empty then self.r and self.w are fully covered
		if not read_remainder and not write_remainder:
			return first, last + 1  # range is [low, last + 1), i.e. last+1 is not selected by the range
		return -2, -2


class AD:
	access_patterns = set()
	shuffles = set()

	def __init__(self, acess_patterns, shuffles):
		self.access_patterns = acess_patterns
		self.shuffles = shuffles

	@staticmethod
	def parse(text):
		text = text[4:-1]
		if text.startswith("A'("):
			ap, text = get_and_remove_up_to_first(text, ')', 3)
			access_pattern = AccessPattern.parse(ap + ')')
		else:
			raise SuggestionSyntaxException("An AD requires at least one access pattern, it may be empty")
		# access_pattern != None otherwise exception is raised

		text = text[1:-1]
		shuffles = set()
		while text.startswith("SH'("):
			text = text[4:]
			shuffle, text = get_and_remove_up_to_first(text, "SH'", 0)
			shuffle = shuffle if shuffle.endswith(')') else shuffle[:-2]
			shuffles.add(SH.parse("SH'(" + shuffle))

		ad = AD({access_pattern}, shuffles)
		ad.merge_overlapping_access_patterns()
		return ad
	
	def size(self):
		total = 0
		for ac in self.access_patterns:
			total += len(ac.r) + len(ac.w)
		return total

	def merge(self, ad):
		self.access_patterns = self.access_patterns | ad.access_patterns
		self.shuffles = self.shuffles | ad.shuffles

	def merge_overlapping_access_patterns(self):
		# merge access paterns that have reads or writes in common
		for ap1 in self.access_patterns:
			for ap2 in self.access_patterns:
				if ap1 == ap2:
					continue
				
				if ap1.r & ap2.r or ap1.w & ap2.w:
					# merge the two access_patterns
					ap1.r = ap1.r | ap2.r
					ap1.w = ap1.w | ap2.w
					ap2.r = ap2.w = set()
		# remove redundant access_patterns
		self.access_patterns = {x for x in self.access_patterns if x.r}

	def fix_conflicting_shuffles(self):
		aps, new_shuffles = SH.find_conflicting(self.shuffles)
		self.shuffles = new_shuffles
		self.access_patterns = self.access_patterns | aps

	def apply(self, composite):
		# apply shuffle suggestions (in-line) until a fixpoint is reached
		shuffled = True
		while shuffled:
			shuffled = False
			for sh in self.shuffles:
				shuffled = shuffled | sh.apply(composite.assignments)
		# move composite statement over the part that requires it
		# first get matching ranges for each access pattern ap
		ranges = []
		for ap in self.access_patterns:
			low, high = ap.find_sub_composite(composite)
			if low != -2:
				ranges.append((low, high))
		# merge overlapping ranges
		for i in range(0, len(ranges)):
			for j in range(0, len(ranges)):
				if i == j:
					continue
				lowi, highi = ranges[i]
				lowj, highj = ranges[j]
				if lowj <= lowi < highj or lowj < highi <= highj:
					# merge range
					new_low = lowi if lowi < lowj else lowj
					new_high = highi if highi > highj else highj
					ranges[i] = (new_low, new_high)
					# 'disable' redundant range
					ranges[j] = (-2,-2)
		ranges = [(low, high) for (low, high) in ranges if low != -2]
		# ranges are now disjoint
		# sort ranges by lowest
		sorted(ranges, key=lambda x: x[0])
		return_statements = []
		asgn_idx = 0
		for r in ranges:
			low, high = r
			if asgn_idx < low:
				return_statements.extend(composite.assignments[asgn_idx:low])
			asgn_idx = high  # next index of assignments
			
			# create new composite class
			composite_class = composite.__class__
			new_composite = composite_class.__new__(composite_class)
			composite_class._tx_metamodel._init_obj_attrs(new_composite)
			
			if low == -1:
				new_composite.guard = composite.guard
				low = 0
			new_composite.assignments = composite.assignments[low:high]
			return_statements.append(new_composite)
		asgn_size = len(composite.assignments)
		if asgn_size > asgn_idx:
			return_statements.extend(composite.assignments[asgn_idx:asgn_size])
		return return_statements


class SH:
	before = None
	after = None

	def __init__(self, before, after):
		self.before = before
		self.after = after

	def __hash__(self):
		return hash((hash(self.before), hash(self.after)))

	@staticmethod
	def parse(text):
		splt = text.split("A'")
		before = AccessPattern.parse("A'" + splt[1][:-2])
		after = AccessPattern.parse("A'" + splt[2][:-1])
		return SH(before, after)

	@staticmethod
	def find_conflicting(shuffle_set):
		access_patterns = set()
		new_shuffles = shuffle_set
		# build a graph dictionary
		graph = dict()
		for sh in shuffle_set:
			for a in sh.before.r:
				acc = (a, None)
				afters = graph.get(acc, set())
				afters = afters | {(x, None) for x in sh.after.r} | {(None, x) for x in sh.after.w}
				graph[acc] = afters
			for a in sh.before.w:
				acc = (None, a)
				afters = graph.get(acc, set())
				afters = afters | {(x, None) for x in sh.after.r} | {(None, x) for x in sh.after.w}
				graph[acc] = afters
		# find a cyclic shuffle orders, we use depth first search
		if graph.keys():
			cycle_completing_edges = find_cycle_completing_edges(graph)
			# remove cycle_completing_edges from the graph
			# and convert removed edges to an access pattern
			for source, target in cycle_completing_edges:
				graph[source].remove(target)
				if not graph[source]:
					del graph[source]
				# convert source, target to an access pattern.
				rsource, wsource = source
				rtarget, wtarget = target
				ap = None
				if rsource and wtarget:
					ap = AccessPattern({rsource}, {wtarget})
				elif wsource and rtarget:
					ap = AccessPattern({rtarget}, {wsource})
				elif wsource and wtarget:
					ap = AccessPattern(set(), {wsource, wtarget})
				if ap:
					access_patterns.add(ap)
			# build new shuffle set
			new_shuffles = set()
			for source, targets in graph.items():
				rsource, wsource = source
				source_ap = AccessPattern({rsource}, set()) if rsource \
							else AccessPattern(set(), {wsource})
				reads = {x for (x, _) in targets if x}
				writes = {x for (_, x) in targets if x}
				target_ap = AccessPattern(reads, writes)
				new_shuffles.add(SH(source_ap, target_ap))
		return access_patterns, new_shuffles

	def apply(self, assignment_list):
		i_after = -1
		shuffled = False
		while True:  # termination condition at first if
			i_after = self.after.find_assignment_full(assignment_list, i_after + 1)
			i_before = self.before.find_assignment_full(assignment_list, i_after + 1)
			
			if i_before == -1 or i_after == -1:
				break
			if i_before > i_after:  # need to swap
				# TODO check whether swap is allowed by conflict-serialisability
				temp = assignment_list[i_before]
				assignment_list[i_before] = assignment_list[i_after]
				assignment_list[i_after] = temp
				assignment_list.insert(i_before, STATEMENT_MEMORY_FENCE)
				shuffled = True
		return shuffled
				


def find_cycle_completing_edges(graph):
	cycle_completing_edges = list()
	visited = set()
	for s in graph.keys():
		if s in visited:
			continue
		
		node_stack = stack()
		node_stack.append(s)
		while node_stack:
			node = node_stack.peek()
			if node in visited:
				# node was already visited
				node_stack.pop()
				continue
			
			visited.add(node)
			targets = graph.get(node, set())
			for target in targets:
				if target not in visited:
					node_stack.append(target)
				elif target in node_stack:
					# if target is visited and in state_stack, then there is a cycle!
					cycle_completing_edges.append((node, target))
	return cycle_completing_edges


from utils import *


STATEMENT_MEMORY_FENCE = ';#;'


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
		write_remainder = (self.r - total_writes)
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
		ad.fix_conflicting_shuffles()
		return ad

	def merge(self, ad):
		self.access_patterns = self.access_patterns | ad.access_patterns
		self.shuffles = self.shuffles | ad.shuffles

	def merge_overlapping_access_patterns(self):
		# TODO merge access paterns that have reads or writes in common
		return

	def fix_conflicting_shuffles(self):
		return
		conflicts = SH.find_conflicting(self.shuffles)
		self.shuffles -= conflicts

	# derive access pattern from conflicting shuffles
	# TODO

	def apply(self, composite):
		statements = []
		# apply shuffle suggestions (in-line)
		for sh in self.shuffles:
			sh.apply(composite.assignments)
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
				lowi = ranges[i][0]
				lowj = ranges[j][0]
				highi = ranges[j][1]
				highj = ranges[j][1]
				if lowj < lowi < highj or lowj < highi < highj:
					# merge range
					ranges[i][0] = lowi if lowi < lowj else lwoj
					ranges[i][1] = highi if highi > highj else highj
					# 'disable' redundant range
					ranges[j][0] = ranges[j][1] = -2
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
			new_composite = Composite()
	todo how to create a composite? can we use textx?
			if low == -1:
				new_composite.guard = composite.guard
				low = 0
			new_composite.assignments = composite.assignments[low:high]
			return_statements.append(new_composite)
		return statements


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
		# find a cyclic shuffle order
		# TODO
		return set()

	def apply(self, assignment_list):
		i_before = -1
		while True:  # termination condition at first if
			i_before = self.before.find_assignment_full(assignment_list, i_before + 1)
			i_after = self.after.find_assignment_full(assignment_list, i_before + 2)
			if i_before == -1 or i_after == -1:
				break
			if i_before > i_after:  # need to swap
				# TODO check whether swap is allowed by conflict-serialisability
				temp = assignment_list[i_before]
				assignment_list[i_before] = assignment_list[i_after]
				assignment_list[i_after] = temp
				assignment_list.insert(i_before, STATEMENT_MEMORY_FENCE)
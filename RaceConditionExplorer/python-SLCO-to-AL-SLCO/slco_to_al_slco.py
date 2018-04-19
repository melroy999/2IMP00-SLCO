# Race Condition Explorer tool, v0.1, 2017
#
# Update History:
#

# Start of program

import argparse
import logging
import logging.config
from collections import Counter
import sys
from os.path import dirname, join
from textx.metamodel import metamodel_from_file
from textx.model import children_of_type

from help_on_error_argument_parser import HelpOnErrorArgumentParser

this_folder = dirname(__file__)
slco_mm = metamodel_from_file(join(this_folder,'slco2.tx'))

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
		return AccessPattern(set(rtxt.split(', ')), set(wtxt.split(', ')))
	
	def find_first_assignment(self, statement_list, start):
		for i in range(start, len(statement_list)):
			statement = statement_list[i]
			b_write_found = len(self.w) == 0 or (len(self.w) == 1 and statement.left.var.name in self.w)
			reads = set()
			get_read_vars_from_expression(statement.right, reads)
			b_reads_found = (reads - self.r) # reads found if result is empty set
			# return if required elements are found
			if b_write_found and b_reads_found:
				return i
		return -1
	
	def find_sub_composite(self, composite):
		# TODO
	

class AD():
	access_patterns = set()
	shuffles = set()

	def __init__(self, acess_patterns, shuffles):
		self.access_patterns = acess_patterns
		self.shuffles = shuffles
	
	@staticmethod
	def parse(text):
		text = text[4:-1]
		access_pattern = None
		if text.startswith("A'("):
			ap, text = get_and_remove_up_to_first(text, ')', 3)
			access_pattern = AccessPattern.parse(ap + ')')
		else:
			raise SuggestionSyntaxException("An AD requires at least one access pattern, it may be empty")
		
		text = text[1:-1]
		shuffles = set()
		while text.startswith("SH'("):
			text = text[4:]
			shuffle, text = get_and_remove_up_to_first(text, "SH'", 0)
			shuffle = shuffle if shuffle.endswith(')') else shuffle[:-2]
			shuffles.add(SH.parse("SH'("+shuffle))
		return AD({access_pattern}, shuffles)
	
	def merge(self, ad):
		self.access_patterns = self.access_patterns | ad.access_patterns
		self.shuffles = self.shuffles | ad.shuffles

	def fix_conflicting_shuffles(self):
		conflicts = SH.find_conflicting(self.shuffles)
		self.shuffles -= conflicts
		# derive access pattern from conflicting shuffles
		#TODO
	
	def apply(self, composite):
		statements = []
		# apply shuffle suggestions (in-line)
		for sh in self.shuffles:
			sh.apply(composite.assignments)
		# apply composite statement on statements needing protection
		# TODO
		
		return statements
	
class SH():
	before = None
	after  = None
	def __init__(self, before, after):
		self.before = before
		self.after  = after
		
	def __hash__(self):
		return hash((hash(self.before), hash(self.after)))
	
	@staticmethod
	def parse(text):
		splt = text.split("A'")
		before = AccessPattern.parse("A'"+splt[1][:-2])
		after = AccessPattern.parse("A'"+splt[2][:-1])
		return SH(before, after)
	
	@staticmethod
	def find_conflicting(shuffle_set):
		# find a cyclic shuffle order
		#TODO
		return set()
	
	def apply(self, assignment_list):
		i_before = -1
		while True: # termination condition at first if
			i_before = self.before.find_first_assignment(assignment_list, i_before + 1)
			i_after  = self.after.find_first_assignment(assignment_list, i_before + 2)
			if i_before == -1 or i_after == -1:
				break
			if i_before > i_after: # need to swap
				temp = assignment_list[i_before]
				assignment_list[i_before] = assignment_list[i_after]
				assignment_list[i_after] = temp


def get_and_remove_up_to_first(string, sub, skip):
	idx = string.find(sub)
	if idx == -1:
		return string, ""
	
	ret1 = string[:idx]
	ret2 = string[idx + skip:]
	return ret1, ret2
	

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
			ad = suggestions.get(statement, AD(set(),set()))
			ad.merge(AD.parse(line))
			suggestions[statement] = ad
	
	for ad in suggestions.values():
		ad.fix_conflicting_shuffles()
	return suggestions


def get_read_vars_from_expression(expr, acc):
	if not expr:
		return
	expr1 = expr.left.left.left.left
	if expr1:
		primary = expr1.left
		if primary and primary.ref:
			acc.add(primary.ref.ref)
	get_read_vars_from_expression(expr.right, acc)
	

#TODO: is the function needed/used?
def get_number_of_reads_and_write(t):
	# count number of reads and write to variables
	assignments = [x for x in t.statements if x.__class__.__name__ == 'Assignment']
	composites = [x for x in t.statements if x.__class__.__name__ == 'Composite']
	for c in composites:
		assignments.extend(c.assignments)
	reads = Counter([])
	for a in assignments:
		get_read_vars_from_expression(a.right, reads)
	for c in composites:
		get_read_vars_from_expression(c.guard, reads)
	writes = Counter([x.left.var.name for x in assignments])
	#print("reads:  " + str(reads))
	#print("writes: " + str(writes))
	return reads, writes


def un_composite_statement_list(statement_list):
	statements = []
	for statement in statement_list:
		if statement.__class__.__name__ != "Composite":
			statements.append(statement)
			continue
		# statement is a Composite statement
		if statement.guard:
			statement.append(statement.guard)
		statements.extend(statement.assignments)
	return statements
	

def translate(model, suggestions):
	print(model.name)
	
	# Currently only 1 class is supported
	global_class = model.classes[0]
	print("class name: "+global_class.name)
	#print([(x.type.base, x.type.size, x.name, x.defvalue, x.defvalues) for x in globalClass.variables])
	global_vars = [x.name for x in global_class.variables]
	
	transitions = children_of_type("Transition", global_class)
	for t in transitions: # TODO: loop over composites instead of transitions
		# print((t.priority, t.source, t.target, t.statements))
		# process suggestions
		ad = suggestions.get(t._tx_position, None)
		if ad: # atomicity violation(s), apply advice
			composites = children_of_type("Composite", t.statements)
			for composite in composites:
				ad.apply(composite)
	
	# We do not support actions
	#model.actions
	# We do not support multiple objects
	#model.objects
	# We do not support channels
	#model.channels
	#globalClass.ports
	return ""

def main():
	# setup logging
	file_handler    = logging.FileHandler(filename='rc_explorer.log', mode='w')
	console_handler = logging.StreamHandler(stream=sys.stdout)
	file_handler.setLevel(logging.INFO)
	console_handler.setLevel(logging.DEBUG)
	logging.basicConfig(format='%(asctime)s - %(levelname)s: %(message)s',
						datefmt='%Y-%m-%d %H:%M:%S',
						level=logging.DEBUG,
						handlers=[file_handler, console_handler])
	
	# parse arguments
	parser = HelpOnErrorArgumentParser(
		description='Core-SLCO to Atomicity-Level-SLCO transformation',
		formatter_class=argparse.ArgumentDefaultsHelpFormatter
	)
	parser.add_argument("INPUT_MODEL", type=str, help="SLCO input model")
	parser.add_argument("INPUT_SUGGESTIONS", type=str, help="Suggestions file generated by mCRL2 analysis")
	parser.add_argument("-o", "--out", type=str, default="INPUT_MODEL", help="Output slco model")
	parser.add_argument("-q", "--quiet", action='store_true', help="Quiet mode, print no messages to screen")
	parser.add_argument("-m", "--mute", action='store_true', help="Mute mode, no messages are printed or logged")
	
	args = vars(parser.parse_args())

	# set options
	if args['quiet']:
		console_handler.setLevel(logging.CRITICAL + 1)

	if args['mute']:
		console_handler.setLevel(logging.CRITICAL + 1)
		file_handler.setLevel(logging.CRITICAL + 1)
	
	slco_path = args['INPUT_MODEL']
	sugg_path = args['INPUT_SUGGESTIONS']
	
	out_path = args['out']
	if out_path == 'INPUT_MODEL':
		out_path = slco_path[:-5] + '_AL.slco'
	elif not out_path.endswith('.slco'):
		out_path = out_path + '.slco'
	
	logging.info('Starting SLCO Atomicity-free code generator')
	logging.info('Input model       : %s', slco_path)
	logging.info('Input suggestions : %s', sugg_path)
	logging.info('Output File       : %s', out_path)

	# read models
	model = slco_mm.model_from_file(slco_path)
	suggestions = parse_suggestions(sugg_path)
	# translate
	out_model = translate(model, suggestions)

	outFile = open(out_path, 'w')
	outFile.write(out_model)
	outFile.close()
	
	logging.info('Finished, output written to %s', out_path)
	logging.shutdown()


if __name__ == '__main__':
	main()

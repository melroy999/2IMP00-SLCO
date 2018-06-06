# Race Condition Explorer tool, v0.1, 2017
#
# Update History:
#

# Start of program

import argparse
import logging
import logging.config
import sys
from os.path import dirname, join
from textx.metamodel import metamodel_from_file
from textx.model import children_of_type

from help_on_error_argument_parser import HelpOnErrorArgumentParser
from suggestions import *

this_folder = dirname(__file__)
slco_mm = metamodel_from_file(join(this_folder,'slco2.tx'))
	

def translate(model, suggestions):
	# Currently only 1 class is supported
	global_class = model.classes[0]
	transitions = []
	for sm in global_class.statemachines:
		for tr in sm.transitions:
			transitions.append(tr)
	#transitions = children_of_type("Transition", global_class)
	for t in transitions:
		#print((t.priority, t.source, t.target, t.statements))
		# process suggestions
		ad = suggestions.get(t._tx_position, None)
		if ad: # atomicity violations, apply advice
			composites = []
			for st in tr.statements:
				if st.__class__.__name__ == "Composite":
					composites.append(st)
			#composites = children_of_type("Composite", t)
			# We assume that a transition only contains one statement.
			# Hence, we can simply assign the new statements
			if composites:
				composite = composites[0]
				t.statements = ad.apply(composite)
	
	# We do not support actions
	#model.actions
	# We do not support multiple objects
	#model.objects
	# We do not support channels
	#model.channels
	#globalClass.ports
	return model

def slco_variable_to_text(var):
	text = ""
	if var.type:
		text += var.type.base
		if var.type.size:
			text += "[%s]" % var.type.size
		text += " "
	text += var.name
	if var.defvalue:
		text += " := %s" % var.defvalue
	elif var.defvalues:
		text += " := [%s]" % ", ".join(str(var.defvalues))
	return text


def slco_var_ref_to_text(ref):
	text = ref.var.name
	if ref.index:
		text += "[%s]" % slco_expression_to_text(ref.index)
	return text


def slco_expression_ref_to_text(ref):
	text = ref.ref
	if ref.index:
		text += slco_expression_to_text(ref.index)
	return text


def slco_primary_to_text(prim):
	text = ""
	if prim.sign:
		text += prim.sign
	if prim.value:
		text += str(prim.value)
	elif prim.body:
		text += "(%s)" % slco_expression_to_text(prim.body)
	elif prim.ref:
		text += slco_expression_ref_to_text(prim.ref)
	return text


def slco_expression1_to_text(expr):
	text = slco_primary_to_text(expr.left)
	if expr.op:
		text += expr.op
		text += slco_expression1_to_text(expr.right)
	return text


def slco_expression2_to_text(expr):
	text = slco_expression1_to_text(expr.left)
	if expr.op:
		text += expr.op
		text += slco_expression2_to_text(expr.right)
	return text


def slco_expression3_to_text(expr):
	text = slco_expression2_to_text(expr.left)
	if expr.op:
		text += expr.op
		text += slco_expression3_to_text(expr.right)
	return text
	

def slco_expression4_to_text(expr):
	text = slco_expression3_to_text(expr.left)
	if expr.op:
		text += expr.op
		text += slco_expression4_to_text(expr.right)
	return text


def slco_expression_to_text(expr):
	text = slco_expression4_to_text(expr.left)
	if expr.op:
		text += expr.op
		text += slco_expression_to_text(expr.right)
	return text


def slco_assignment_to_text(assign):
	if assign.__class__.__name__ == "str":  # in case of MemoryFence #
		return assign
	return "%s := %s" % (slco_var_ref_to_text(assign.left), slco_expression_to_text(assign.right))


def slco_statement_to_text(statement):
	if statement.__class__.__name__ == "Assignment":
		text = slco_assignment_to_text(statement)
	elif statement.__class__.__name__ == "Composite":
		assignments = [slco_assignment_to_text(x) for x in statement.assignments]
		if statement.guard:
			assignments.insert(0, slco_expression_to_text(statement.guard))
		text = "[%s]" % "; ".join(assignments)
	elif statement.__class__.__name__ == "Expression":
		text = slco_expression_to_text(statement)
	else:
		text = statement
	
	return text


transition_template = '''from %s to %s {
						%s
					}\n'''

def slco_transition_to_text(transition):
	text = ""
	if transition.priority:
		text += "%s : " % transition.priority
	statements = [slco_statement_to_text(x) for x in transition.statements]
	text += transition_template % \
	        (transition.source.name, transition.target.name, " ; ".join(statements))
	return text


state_machine_template = '''%s {
				variables
					%s
				initial %s
				states  %s
				transitions
					%s
				}'''


def slc_state_machine_to_text(state_machine):
	variables = [slco_variable_to_text(x) for x in state_machine.variables]
	states = [x.name for x in state_machine.states]
	transitions = [slco_transition_to_text(x) for x in state_machine.transitions]
	return state_machine_template % \
	       (state_machine.name, "\n\t\t\t\t\t".join(variables), state_machine.initialstate.name,
		    " ".join(states),  "\n\t\t\t\t\t".join(transitions))
	
	
slco_template = """model al_%s {
classes
	GlobalClass {
		variables
			%s
		
		state machines
			%s
	}

objects
	globalObject : GlobalClass()
}
"""


def al_slco_model_to_file(model, path):
	global_class = model.classes[0]
	variables = [slco_variable_to_text(x) for x in global_class.variables]
	state_machines = [slc_state_machine_to_text(x) for x in global_class.statemachines]
	
	text = slco_template % (model.name, "\n\t\t\t".join(variables), "\n\n\t\t\t".join(state_machines))
	outFile = open(path, 'w')
	outFile.write(text)
	outFile.close()

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
		out_path = slco_path[:-5] + '.alslco'
	elif not out_path.endswith('.alslco'):
		out_path = out_path + '.alslco'
	
	logging.info('Starting SLCO Atomicity-free code generator')
	logging.info('Input model       : %s', slco_path)
	logging.info('Input suggestions : %s', sugg_path)
	logging.info('Output File       : %s', out_path)

	# read models
	model = slco_mm.model_from_file(slco_path)
	suggestions = parse_suggestions(sugg_path)
	# translate
	out_model = translate(model, suggestions)
	# write output to file
	al_slco_model_to_file(out_model, out_path)
	
	logging.info('Finished, output written to %s', out_path)
	logging.shutdown()


if __name__ == '__main__':
	main()

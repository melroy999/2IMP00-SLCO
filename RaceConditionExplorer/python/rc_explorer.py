# Race Condition Explorer tool, v0.1, 2017
#
# Update History:
#

# Start of program

import argparse
import logging
import logging.config
import os
import re
import sys
from lts import *
from VarDependencyGraph import VarDependencyGraph

from help_on_error_argument_parser import HelpOnErrorArgumentParser

# matching of RW actions
GROUP_OBJECT     = 'obj'
GROUP_READ_VARS  = 'reads'
GROUP_WRITE_VARS = 'writes'

action_matcher = re.compile('RW_(?P<'+GROUP_OBJECT+'>[\w|.]+)[!|(][{](?P<'+GROUP_READ_VARS+'>\w?([,]\w)*)[}],[{](?P<'+GROUP_WRITE_VARS+'>\w?([,]\w)*)[}]')


def RCE_get_race_conditions_from_file(path):
	lts = LTS.create(path)
	LTS_remove_peek(lts)
	lts.minimise(LTS.Equivalence.BRANCHING_BISIM)
	locks = get_race_conditions(lts)
	for lock in locks:
		print(lock)


# precondition: peeks are removed from the LTS
def get_race_conditions(lts):
	transitions = lts.transition_dict
	locks = set()
	for src, trans in transitions.items():
		rw_list = []
		# get read/write actions
		for a, tgts in trans.items():
			if a.startswith('RW_'):
				match_result = action_matcher.match(a)
				if not match_result:
					logging.error('action label \"%s\" does not adhere to the required format: RW_<ID>.<SUB_ID>({<set of reads>}, {<set of writes>})' % a)
					continue
				
				obj_id = match_result.group(GROUP_OBJECT)
				read_vars  = set(match_result.group(GROUP_READ_VARS).split(',')) - {''}
				write_vars = set(match_result.group(GROUP_WRITE_VARS).split(',')) - {''}
				#read_vars  = {obj_id + '.' + var for var in read_vars}
				#write_vars = {obj_id + '.' + var for var in write_vars}
				rw_list.append((a, read_vars, write_vars))
				
		# analyse read/write performed by src state
		dep_lts = VarDependencyGraph(rw_list)
		locked, locked_sets = dep_lts.calculate_locks()
		flat_locked_sets = {x for locked_set in locked_sets for x in locked_set}
		locks |= locked_sets | {frozenset(x) for x in locked if x not in flat_locked_sets}
	return locks
	
	
def LTS_remove_peek(lts):
	temp_act = 'temp_tau'
	lts.rename_action_labels({'tau': temp_act})
	lts.hide_action_labels({'peek.*'})
	lts.minimise(LTS.Equivalence.WEAK_BISIM)
	lts.rename_action_labels({temp_act: 'tau'})


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
		description='Race Condition Explorer: finds race conditions in state spaces in aut format, where labels are formatted as RW_Object(Read set, Write set)',
		formatter_class=argparse.ArgumentDefaultsHelpFormatter
	)
	parser.add_argument("INPUT_LTS", type=str, help="LTS file in aut format")
	parser.add_argument("-o", "--out", type=str, default="INPUT_LTS.rc", help="Output file name")
	parser.add_argument("-q", "--quiet", action='store_true', help="Quiet mode, print no messages to screen")
	
	args = vars(parser.parse_args())
	
	# set options
	if args['quiet']:
		console_handler.setLevel(logging.CRITICAL + 1)
	
	lts_path = args['INPUT_LTS']
	if not lts_path.endswith('.aut'):
		lts_path = lts_path + ".aut"
	
	out_path = args['out']
	if out_path == 'INPUT_LTS.rc':
		out_path = lts_path[:-4] + '.rc'
	
	logging.info('Starting Race Condition Explorer')
	logging.info('Input LTS  : %s', lts_path)
	logging.info('Output File: %s', out_path)
	
	RCE_get_race_conditions_from_file(lts_path)
	
	logging.info('Finished, output written to %s', out_path)
	logging.shutdown()


if __name__ == '__main__':
	main()

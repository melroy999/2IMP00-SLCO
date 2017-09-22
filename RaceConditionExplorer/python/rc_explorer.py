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
GROUP_SRC_OBJECT        = 'src_obj'
GROUP_TGT_OBJECT        = 'tgt_obj'
GROUP_SRC_READ_VARS     = 'src_reads'
GROUP_TGT_READ_VARS     = 'tgt_reads'
GROUP_SRC_WRITE_VARS    = 'src_writes'
GROUP_TGT_WRITE_VARS    = 'tgt_writes'
GROUP_SRC_STATE_MACHINE = 'src_sm'
GROUP_TGT_STATE_MACHINE = 'tgt_sm'
GROUP_PORT              = 'port'

action_matcher = re.compile('RW_(?P<'+GROUP_SRC_OBJECT+'>\w+)'
							'[(](?P<'+GROUP_SRC_STATE_MACHINE+'>\w+),'
							'[{](?P<'+GROUP_SRC_READ_VARS+'>\w?([,]\w)*)[}],'
							'[{](?P<'+GROUP_SRC_WRITE_VARS+'>\w?([,]\w)*)[}]')

# 'RW'
# 'send'
# 'receive'
# 'peek'
# 'comm'
#
# '_(?P<'+GROUP_SRC_OBJECT+'>\w+)' # all
# '\'(?P<'+GROUP_PORT+'>\w+)' # send, receive, peek, comm
#
# '_(?P<'+GROUP_TGT_OBJECT+'>\w+)' # peek & comm
# '\'(?P<'+GROUP_PORT+'>\w+)' # peek & comm
#
# '[(](?P<'+GROUP_SRC_STATE_MACHINE+'>\w+),' # all
# '[{](?P<'+GROUP_SRC_READ_VARS+'>\w?([,]\w)*)[}],' #all
# '[{](?P<'+GROUP_SRC_WRITE_VARS+'>\w?([,]\w)*)[}],' # all
# '(?P<'+GROUP_TGT_STATE_MACHINE+'>\w+),' # send, receive, peek, comm
# '[{](?P<'+GROUP_TGT_READ_VARS+'>\w?([,]\w)*)[}],' # send, receive, peek, comm
# '[{](?P<'+GROUP_TGT_WRITE_VARS+'>\w?([,]\w)*)[}]' # send, receive, peek, comm

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
	dep_ltss = dict()
	for src, trans in transitions.items():
		rw_list = []
		signature = set() # a set of all outgoing edges that are relevant for race condition detection
		# get read/write actions
		for a, tgts in trans.items():
			if a.startswith('RW_'):
				match_result = action_matcher.match(a)
				if not match_result:
					logging.error('action label \"%s\" does not adhere to the required format: RW_<ID>.<SUB_ID>({<set of reads>}, {<set of writes>})' % a)
					continue
				
				obj_id = match_result.group(GROUP_SRC_OBJECT)
				sm_id = match_result.group(GROUP_SRC_STATE_MACHINE)
				read_vars  = set(match_result.group(GROUP_SRC_READ_VARS).split(',')) - {''}
				write_vars = set(match_result.group(GROUP_SRC_WRITE_VARS).split(',')) - {''}
				read_vars  = {obj_id + '.' + var for var in read_vars}  # add object owning the variable
				write_vars = {obj_id + '.' + var for var in write_vars} # add object owning the variable
				rw_list.append((a, sm_id, read_vars, write_vars))
				signature.add(a)
				
		# analyse read/write performed by src state
		frozen_signature = frozenset(signature)
		if frozen_signature not in dep_ltss:
			dep_ltss[frozen_signature] = VarDependencyGraph(rw_list)
	
	
	for dep_lts in dep_ltss.values():
		print(dep_lts.find_cycles())
	
	print()
	locked_sets = set()
	for dep_lts in dep_ltss.values():
		locked_sets |= (dep_lts.get_locked_sets())
		
	# flatten lock_set
	flat_locked_sets = {x for locked_set in locked_sets for x in locked_set}
	
	# calculate further locks
	locked = set(flat_locked_sets)
	for dep_lts in dep_ltss.values():
		# locked is both used as set of existing locks and as accumulator of locks
		dep_lts.get_locked(locked)
	
	return locked_sets | {frozenset([x]) for x in locked if x not in flat_locked_sets}
	
	
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

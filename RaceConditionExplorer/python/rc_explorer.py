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
import time

from help_on_error_argument_parser import HelpOnErrorArgumentParser

# matching of actions
GROUP_LABEL             = 'label'
GROUP_SRC_OBJECT        = 'src_obj'
GROUP_TGT_OBJECT        = 'tgt_obj'
GROUP_SRC_READ_VARS     = 'src_reads'
GROUP_TGT_READ_VARS     = 'tgt_reads'
GROUP_SRC_WRITE_VARS    = 'src_writes'
GROUP_TGT_WRITE_VARS    = 'tgt_writes'
GROUP_SRC_STATE_MACHINE = 'src_sm'
GROUP_TGT_STATE_MACHINE = 'tgt_sm'
GROUP_SRC_PORT          = 'src_port'
GROUP_TGT_PORT          = 'tgt_port'
GROUP_MSG               = 'sg'

#action_matcher = re.compile('RW_(?P<'+GROUP_SRC_OBJECT+'>\w+)'
#							'[(](?P<'+GROUP_SRC_STATE_MACHINE+'>\w+),'
#							'[{](?P<'+GROUP_SRC_READ_VARS+'>\w?([,]\w)*)[}],'
#							'[{](?P<'+GROUP_SRC_WRITE_VARS+'>\w?([,]\w)*)[}]')


action_matcher = re.compile('(?P<'+GROUP_LABEL+'>rw|send|receive|peek|comm)'
							'_(?P<'+GROUP_SRC_OBJECT+'>[a-zA-Z0-9]+)'

							'(_(?P<'+GROUP_SRC_PORT+'>[a-zA-Z0-9]+))?'

							'(_(?P<'+GROUP_TGT_OBJECT+'>[a-zA-Z0-9]+)_(?P<'+GROUP_TGT_PORT+'>[a-zA-Z0-9]+))?'

							'[(](?P<'+GROUP_SRC_STATE_MACHINE+'>\w+),'
							'[{](?P<'+GROUP_SRC_READ_VARS+'>(\w+([(]\d[)])?)?([,]\w+([(]\d[)])?)*)[}],'
							'[{](?P<'+GROUP_SRC_WRITE_VARS+'>(\w+([(]\d[)])?)?([,]\w+([(]\d[)])?)*)[}]'

							'(,(?P<'+GROUP_TGT_STATE_MACHINE+'>\w+),'
							'[{](?P<'+GROUP_TGT_READ_VARS+'>(\w+([(]\d[)])?)?([,]\w+([(]\d[)])?)*)[}],'
							'[{](?P<'+GROUP_TGT_WRITE_VARS+'>(\w+([(]\d[)])?)?([,]\w+([(]\d[)])?)*)[}],'
							'(?P<'+GROUP_MSG+'>\w+).*[)])?')

class ActionSyntaxException(Exception):
	def __init__(self, value):
		self.parameter = value
	def __str__(self):
		return repr(self.parameter)


def RCE_get_race_conditions_from_file(path):
	lts = LTS.create(path)
	#lts = LTS_remove_peek(lts)
	#lts = lts.minimise(LTS.Equivalence.BRANCHING_BISIM)
	start = time.time()
	dep_ltss, locked = get_dependency_ltss(lts)
	cycle_sets = get_cycle_sets(dep_ltss)
	logging.info("cycle_sets: %s" % cycle_sets)
	locks = get_race_conditions(dep_ltss, locked)
	logging.info("locks: %s" % locks)
	end = time.time()
	print("Analysis took " + str(end - start))
	return locks
	
	
# precondition: peeks are removed from the LTS
def get_dependency_ltss(lts):
	### Begin switch "append_rw" ###
	# absence of ports are ignored as they do not contribute to the dependency ltss
	# a postfix is added to the action label to ensure two nodes for the comm action
	# and consistent naming for the nodes
	def append_standard():
		rw_list.append((a + src_obj + src_sm, src_sm, src_read_vars, src_write_vars))
	
	def append_receive():
		if (tgt_pre is None) or (tgt_sm is None) or (tgt_read is None) or (tgt_write is None):
			raise ActionSyntaxException(
				'action label \"%s\" is missing value for target state_machine, read, and/or write.' % a)
		rw_list.append((a + tgt_pre + tgt_sm, tgt_sm, tgt_read_vars, tgt_write_vars))
	
	def append_comm():
		append_standard()
		append_receive()
	
	append_rw = {'rw': append_standard, 'send': append_standard, 'receive': append_receive,
		'peek': append_standard, 'comm': append_comm}
	### End switch ###
	
	transitions = lts.transition_dict
	dep_ltss = dict()
	for src, trans in transitions.items():
		rw_list = []
		signature = set()  # a set of all outgoing edges that are relevant for race condition detection
		# get read/write actions
		for a, tgts in trans.items():
			if a.startswith('tau'):
				continue
			
			match_result = action_matcher.match(a)
			if not match_result:
				raise ActionSyntaxException('action label \"%s\" does not match the required format.' % a)
				
			label = match_result.group(GROUP_LABEL)
			
			src_obj  = match_result.group(GROUP_SRC_OBJECT)
			src_sm   = match_result.group(GROUP_SRC_STATE_MACHINE)
			src_port = match_result.group(GROUP_SRC_PORT)
			tgt_obj  = match_result.group(GROUP_TGT_OBJECT)
			tgt_sm   = match_result.group(GROUP_TGT_STATE_MACHINE)
			tgt_port = match_result.group(GROUP_TGT_PORT)
			
			src_read  = match_result.group(GROUP_SRC_READ_VARS)
			src_write = match_result.group(GROUP_SRC_WRITE_VARS)
			tgt_read  = match_result.group(GROUP_TGT_READ_VARS)
			tgt_write = match_result.group(GROUP_TGT_WRITE_VARS)
			
			#msg = match_result.group(GROUP_MSG)
			
			src_read_vars  = set(src_read.split(',')) - {''}
			src_write_vars = set(src_write.split(',')) - {''}
			tgt_read_vars = set(tgt_read.split(',')) - {''} if tgt_read else set()
			tgt_write_vars = set(tgt_write.split(',')) - {''} if tgt_write else set()
			
			# add object owning the variable
			tgt_pre = src_obj if label == 'receive' else tgt_obj
			src_read_vars  = {src_obj + '.' + var for var in src_read_vars}
			src_write_vars = {src_obj + '.' + var for var in src_write_vars}
			tgt_read_vars  = {tgt_pre + '.' + var for var in tgt_read_vars}
			tgt_write_vars = {tgt_pre + '.' + var for var in tgt_write_vars}
			
			append_rw[label]() # switch on label to push to rw_list
			signature.add(a)
		
		# analyse read/write performed by src state
		frozen_signature = frozenset(signature)
		locked = set()
		if frozen_signature not in dep_ltss:
			dep_ltss[frozen_signature] = VarDependencyGraph(rw_list, locked)
	return (dep_ltss, locked)


def get_race_conditions(dep_ltss, pre_locked):
	locked_sets = set()
	for dep_lts in dep_ltss.values():
		locked_sets |= (dep_lts.get_locked_sets())
		
	# flatten lock_set
	flat_locked_sets = {x for locked_set in locked_sets for x in locked_set}
	
	# calculate further locks
	locked = set(flat_locked_sets) | pre_locked
	for dep_lts in dep_ltss.values():
		# locked is both used as set of existing locks and as accumulator of locks
		dep_lts.get_locked(locked)
	
	return locked_sets | {frozenset([x]) for x in locked if x not in flat_locked_sets}


def get_cycle_sets(dep_ltss):
	cycles = set()
	for dep_lts in dep_ltss.values():
		cycles |= dep_lts.find_cycles()
	cycles -= set()  # ensure empty set is not present
	return cycles  # TODO: apply Hitting set problem algorithm to find smallest set of locks

	
def LTS_remove_peek(my_lts):
	temp_act = 'temp_tau'
	my_lts.rename_action_labels({'tau': temp_act})
	my_lts.hide_action_labels({'peek_[a-zA-Z0-9]+_[a-zA-Z0-9]+[(].*'})
	my_lts = my_lts.minimise(LTS.Equivalence.WEAK_BISIM)
	my_lts.rename_action_labels({temp_act: 'tau'})
	return my_lts


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
		description='Race Condition Explorer: finds race conditions in state spaces in aut format, where labels are formatted as rw_Object(Read set, Write set)',
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
	
	locks = RCE_get_race_conditions_from_file(lts_path)
	object_locks = {}
	for lock in locks:
		it = iter(lock)
		x = next(it)
		obj, _, var = x.partition('.')
		combo_lock = [var]
		for x in it:
			_, _, var = x.partition('.')
			combo_lock.append(var)
		lock_list = object_locks.get(obj, [])
		lock_list.append(combo_lock)
		object_locks[obj] = lock_list
	f = open(out_path, 'w')
	for obj, locks in object_locks.items():
		f.write(obj+":\n")
		for lock in locks:
			f.write("\t%s\n" % ",".join(lock))
	f.close()
	
	logging.info('Finished, output written to %s', out_path)
	logging.shutdown()


if __name__ == '__main__':
	main()

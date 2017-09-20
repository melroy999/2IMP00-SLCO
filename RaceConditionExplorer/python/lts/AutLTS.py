from .lts import LTS, ISuportLabelRename, ISupportLabelHide, ISupportMinimise, _lts_factories
from . import aut
from . import mcrl2
import os
import re

_equivalence_dict = {   LTS.Equivalence.WEAK_BISIM      : mcrl2.WEAK_BISIM,
						LTS.Equivalence.BRANCHING_BISIM : mcrl2.BRANCHING_BISIM
					}


class AutLTS(   LTS,
			    ISupportMinimise,
				ISupportLabelHide,
				ISuportLabelRename):
	_init_state = 0
	_num_states = 0
	_num_trans = 0
	_transitions = dict()
	_action_labels = list()
	
	def __init__(self, init_state, num_states, num_trans, transitions, action_labels):
		self._init_state    = init_state
		self._num_states    = num_states
		self._num_trans     = num_trans
		self._transitions   = transitions
		self._action_labels = action_labels
	
	
	@property
	def num_states(self):
		return self._num_states
	
	
	@property
	def num_transitions(self):
		return self._num_states
	
	
	@property
	def transition_dict(self):
		return self._transitions
	
	
	def hide_action_labels(self,hiding_set):
		hiding_res = map(re.compile,hiding_set)
		for src, trans in self._transitions.items():
			for a, tgts in trans.items():
				for rex in hiding_res:
					m = rex.match(a)
					if m:
						tau_tgts = trans.get('tau', set())
						tau_tgts = tau_tgts | tgts
						trans['tau'] = tgts
						break
		pass
	
	
	def rename_action_labels(self, rename_dict):
		for src, trans in self._transitions.iteritems():
			# loop over transitions; making use of items() to get a copy of (key, value) pairs such that old actions may be deleted
			for a, tgts in trans.items():
				new_a = rename_dict.get(a)
				if new_a:
					trans[new_a] = tgts
					del trans[a]
					
				
		
	#	@abstractmethod
	#	def get_transitions(self):
	#		pass
	
	
	def minimise(self,equivalence):
		filename = os.path.join(self._folder, self._filename+'.aut')
		temp_path = self._folder + self._filename + '.temp' + self._ext
		
	
	
	def write_to_file(self, path):
		folder, name = os.path.split(path)
		header = [self._init_state, self._num_trans, self._num_states]
		aut.write(folder, header, self._transitions)
	
	
	@classmethod
	def minimise_lts_file(cls, input, output, equivalence):
		mcrl2.minimize(input, output, _equivalence_dict[equivalence])
	
	
	@staticmethod
	def _read_from_file(path):
		folder, name = os.path.split(path)
		header, trans, labels = aut.read(folder,name)
		return AutLTS(header[0], header[2], header[1], trans, labels)


# register AutLTS as read/writer for .aut files
_lts_factories['.aut'] = AutLTS._read_from_file
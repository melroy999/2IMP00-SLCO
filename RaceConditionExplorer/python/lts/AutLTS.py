from .lts import LTS, ISuportLabelRename, ISupportLabelHide, ISupportMinimise, _lts_factories
from . import aut
from . import mcrl2
import os
import re




class AutLTS(   LTS,
			    ISupportMinimise,
				ISupportLabelHide,
				ISuportLabelRename):
	_init_state = 0
	_transitions = dict()
	_action_labels = list()
	
	def __init__(self, init_state, transitions, action_labels):
		self._init_state    = init_state
		self._transitions   = transitions
		self._action_labels = action_labels
	
	@property
	def num_states(self):
		states = set(self._transitions.keys())
		for trans in self._transitions.values():
			for tgt in trans.values():
				states |= tgt
		return len(states)
	
	@property
	def num_transitions(self):
		counter = 0
		for trans in self._transitions.values():
			for tgt in trans.values():
				counter += len(tgt)
		return counter
	
	
	@property
	def transition_dict(self):
		return self._transitions
	

	def hide_action_labels(self,hiding_set):
		hiding_res = [re.compile(x) for x in hiding_set]
		for src, trans in self._transitions.items():
			for a in list(trans.keys()):
				for rex in hiding_res:
					m = rex.match(a)
					if m:
						tau_tgts = trans.get('tau', set())
						tau_tgts |= trans[a]
						trans['tau'] = tau_tgts
						del trans[a]
						break
	
	
	def rename_action_labels(self, rename_dict):
		for src, trans in self._transitions.items():
			for a in list(trans.keys()):
				new_a = rename_dict.get(a)
				if new_a:
					targets = trans.get(new_a, set())
					trans[new_a] = targets | trans[a]
					del trans[a]
	
	
	def write_to_file(self, path):
		folder, name = os.path.split(path)
		header = [self._init_state, str(self.num_transitions), str(self.num_states)]
		aut.write(folder, header, self._transitions, name)
	
	
	def minimise(self,equivalence):
		temp_path_in = os.path.join(self._folder, self._filename + '.temp_min_in')
		self.write_to_file(temp_path_in)
		temp_path_in += self._ext
		temp_path_out = os.path.join(self._folder, self._filename + '.temp_min_out' + self._ext)
		
		self.minimise_lts_file(temp_path_in, temp_path_out, equivalence)
		lts = LTS.create(temp_path_out)
		return lts
		os.remove(temp_path_in)
		os.remove(temp_path_out)
	
	
	@classmethod
	def minimise_lts_file(cls, input, output, equivalence):
		mcrl2.minimize(input, output, equivalence)
	
	
	@staticmethod
	def _read_from_file(path):
		folder, name = os.path.split(path)
		header, trans, labels = aut.read(folder,name)
		return AutLTS(header[0], trans, labels)


# register AutLTS as read/writer for .aut files
_lts_factories['.aut'] = AutLTS._read_from_file

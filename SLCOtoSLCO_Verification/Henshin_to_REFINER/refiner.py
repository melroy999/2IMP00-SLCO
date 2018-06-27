
class LTS:

	transitions = []

	def add_transition(self, source, action, target):
		self.transitions.add((source, action, target))

	def get_states(self):
		states = set()
		for s, _, t in self.transitions:
			states.add(s)
			states.add(t)
		return states

	def to_string(self):
		num_states = len(self.get_states())
		# TODO; what are the 3rd and 4th elements of des header?
		header = "des(%s,%s,2,0)\n" % (len(self.transitions), num_states)
		trans = ['(%s,"%s",%s)' % (s, a, t) for s, a, t in self.transitions]
		return header + "\n".join(trans)




class RuleSystem:
	rules = []
	sync_left = []
	sync_right = []

	def to_string(self):
		str_rules = [r.to_string() for r in self.rules]
		str_sync_left = [l.to_str() for l in self.sync_left]
		str_sync_right = [l.to_str() for l in self.sync_right]
		return "transform\n%s\n\nadd\nsynch left\n\n%ssynch right\n%s" % \
			("\n\n".join(str_rules), "\n".join(str_sync_left), "\n".join(str_sync_right))



class Rule:
	L = None
	R = None

	def __init__(self, L, R):
		self.L = L
		self.R = R

	def to_string(self):
		return "%s\n->\n%s" % (self.L.to_string(), self.R.to_string())


class Law:
	t = set()
	a = ""

	def __hash__(self):
		return hash((self.t, self.a))

	def to_string(self):
		return "%s -> %s" % (" ".join(self.t), self.a)


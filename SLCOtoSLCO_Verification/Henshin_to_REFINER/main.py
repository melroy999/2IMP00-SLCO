import sys
import refiner
import pyecore.ecore as Ecore
import textualSlco as SLCO
import henshin
from pyecore.resources import ResourceSet, URI


EXT = ".henshin"
HENSHIN_URI = "http://www.eclipse.org/emf/2011/Henshin"


class ElementNotSupportedException(Exception):
	def __init__(self, message):
		# Call the base class constructor with the parameters it needs
		super().__init__(message)


def eproxy_to_slco(eproxy):
	eproxy.force_resolve()


	return None

def hensin_graph_to_lts(g):
	nodes = {n: eproxy_to_slco(n.type) for n in g.nodes}



	return refiner.LTS()


def henshin_rule_to_refiner_rule(rule):
	ref_laws_L = []
	ref_laws_R = []

	L = hensin_graph_to_lts(rule.lhs)
	R = hensin_graph_to_lts(rule.rhs)

	ref_rule = refiner.Rule(L, R)
	return ref_rule, ref_laws_L, ref_laws_R


def henshin_to_rulesystem(hroot):
	rules = []
	for unit in hroot.units:
		# if not unit.activated:
		# 	continue
		if not isinstance(unit, henshin.Rule):
			raise ElementNotSupportedException("Only 'Rule' elements are allowed in the transformation specification")
		# if not unit.checkDangling:
		# 	raise ElementNotSupportedException("Only 'Rule' elements with 'checkDangling=true' are allowed")
		# if not unit.injectiveMatching:
		# 	raise ElementNotSupportedException("Only 'Rule' elements with 'injectiveMatching=true' are allowed")
		rules.append(unit)

	rule_system = refiner.RuleSystem()
	for rule in rules:
		ref_rule, ref_laws_L, ref_laws_R = henshin_rule_to_refiner_rule(rule)
		rule_system.rules.append(ref_rule)
		rule_system.sync_left.add(ref_laws_L)
		rule_system.sync_right.add(ref_laws_R)

	return rule_system


def main(args):
	"""The main function"""

	output_filename = ""
	if len(args) > 0:
		if args[0] == '-h' or args[0] == '-help':
			print("Usage: pypy/python3 main <henshin_file>")
			print("")
			print("Extract SLCO/REFINER semantics from henchin file.")
			sys.exit(0)

	input_file = args[0]
	if not input_file.endswith(EXT):
		input_file = input_file + EXT

	output_file = input_file[:-len(EXT)] + ".rs"
	print("Input: %s" % input_file)
	print("Output: %s" % output_file)

	rset = ResourceSet()
	rset.metamodel_registry[Ecore.nsURI] = Ecore
	rset.metamodel_registry[henshin.nsURI] = henshin
	rset.metamodel_registry[SLCO.nsURI] = SLCO

	input_model = rset.get_resource(input_file)
	root_module = input_model.contents[0]
	rs = henshin_to_rulesystem(root_module)
	f = open(output_file, 'w')
	f.write(rs.to_string())
	f.close()


if __name__ == '__main__':
	args = []
	for i in range(1, len(sys.argv)):
		args.append(sys.argv[i])
	main(args)

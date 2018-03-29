import sys
from os.path import dirname, basename, join, exists
from os import mkdir
from textx.metamodel import metamodel_from_file
from shutil import rmtree
import json
import random
import igraph # pip install python-igraph
import math
import sys

modelname = ""
this_folder = dirname(__file__)

local_var_idx = sys.maxsize

class MinMax:
	min = 0
	max = 0
	
	def __init__(self, min, max):
		self.min = min
		self.max = max
		
	def randint(self):
		return random.randint(self.min, self.max)
	
	def uniform(self):
		return random.uniform(self.min, self.max)
	
	
class GraphGenerator:
	def generate(self):
		return None
	
class GraphGenerator_Static_Power_Law(GraphGenerator):
	num_nodes    = MinMax(1,1)
	num_edges    = MinMax(1,1)
	exponent_out = MinMax(1.0,1.0)
	exponent_in  = MinMax(1.0,1.0)
	
	def generate(self):
		return igraph.Graph.Static_Power_Law(
			self.num_nodes.randint(),
			self.num_edges.randint(),
			self.exponent_out.uniform(),
			self.exponent_in.uniform(),
			loops=True, multiple=False)


class GraphGenerator_Erdos_Renyi(GraphGenerator):
	edge_probability = MinMax(0.0, 1.0)
	num_nodes = MinMax(1, 1)
	
	def generate(self):
		return (False, igraph.Graph.Erdos_Renyi(self.num_nodes.randint, self.edge_probability.randint(), directed=True, loops=True))


class GraphGenerator_SCC(GraphGenerator):
	degree_range = MinMax(1, 1)
	num_nodes = MinMax(1, 1)
	num_edges = MinMax(1, 1)

	
	def spanning_tree_to_directed_graph(st):
		g = igraph.Graph()
		n = st.vcount()
		g.add_vertices(n)
		
		# Pre-order walk of spanning-tree
		vertices_to_process = [0]
		while vertices_to_process:
			v = vertices_to_process.pop()
			edges = st.incident(v, igraph.ALL)
			for e in edges:
				t = e.target if e.source == v else e.source
				g.add_edge(v, t)
				vertices_to_process.append(t)
		return g
		
	def generate(self):
		# generate a minimum spanning tree with n nodes
		n = self.num_nodes.randint()
		out_degree = []
		sum = 0
		for i in range(1,n-1):
			d = self.degree_range.randint()
			sum += d
			out_degree.append(d)
		# make sum of degrees even
		d = self.degree_range.randint()
		if sum % 2 != d % 2:
			d += 1
		out_degree.append(d)
		temp = igraph.Graph.Degree_Sequence(out_degree, method="vl")
		g = GraphGenerator_SCC.spanning_tree_to_directed_graph(temp.spanning_tree())
		n_edges = self.num_edges.randint()
		actual_n_edges = g.ecount()
		if actual_n_edges < n_edges:
			# we want to favor vertices with high degree
			# we shall select vertices from a list in which a vertex occurs as many times as its degree
			selection_list = []
			for i in range(0,n):
				d = g.degree(i,loops=False)
				selection_list.append([i]*d)
			# add edges until the desired number of edges is reached
			while actual_n_edges < n_edges:
				source = selection_list[random.randint(0, len(selection_list))]
				target = selection_list[random.randint(0, len(selection_list))]
				selection_list.append(source)
				selection_list.append(target)
				g.add_edge(source, target)
				actual_n_edges += 1
		return True, g
	
	
class GraphGeneratorMixed(GraphGenerator):
	gen_list = [GraphGenerator_Erdos_Renyi(), GraphGenerator_Static_Power_Law()]
	
	def generate(self):
		i = random.randint(0,len(gen_list))
		return gen_list[i].generate()


class Config:
	num_models_to_generate = 1
	model_name             = "gen_"
	num_state_machines     = MinMax(1,1)
	statement_size         = MinMax(1,1)
	sm_gen_method          = GraphGeneratorMixed()
	num_vars_shared_by_more_than_two_sms = MinMax(0, 0)
	
	@staticmethod
	def fromFile(path):
		file = open(path, 'r')
		config = json.load(file, object_hook=from_json)
		file.close()
		return config
	
	def writeToFile(self, path):
		file = open(path, 'w')
		tmp = self.num_models_to_generate
		json.dump(self, file, default=to_json, indent=4)
		file.close()


def to_json(obj):
	if isinstance(obj, Config):
		return {'__class__' : 'Config',
				'num_models_to_generate' : obj.num_models_to_generate,
				'model_name_prefix'      : obj.model_name,
				'num_state_machines'     : to_json(obj.num_state_machines),
				'statement_size'         : to_json(obj.statement_size),
				'sm_gen_method'          : to_json(obj.sm_gen_method),
				'num_vars_shared_by_more_than_two_sms' : to_json(obj.num_vars_shared_by_more_than_two_sms)}
	elif isinstance(obj, MinMax):
		return {'__class__' : 'MinMax',
				'min' : obj.min,
				'max' : obj.max }
	elif isinstance(obj, GraphGeneratorMixed):
		return {'__class__' : 'GraphGeneratorMixed',
				'generator_list' : obj.gen_list}
	elif isinstance(obj, GraphGenerator_Erdos_Renyi):
		return {'__class__'        : 'GraphGenerator_Erdos_Renyi',
				'edge_probability' : to_json(obj.edge_probability),
				'num_nodes'        : to_json(obj.num_nodes) }
	elif isinstance(obj, GraphGenerator_Static_Power_Law):
		return {'__class__'    : 'GraphGenerator_Static_Power_Law',
				'num_nodes'    : to_json(obj.num_nodes),
				'num_edges'    : to_json(obj.num_edges),
				'exponent_out' : to_json(obj.exponent_out),
				'exponent_in'  : to_json(obj.exponent_in) }
	elif isinstance(obj, GraphGenerator_SCC):
		return {'__class__': 'GraphGenerator_SCC',
				'degree_range': to_json(obj.exponent_out),
				'num_nodes': to_json(obj.num_nodes),
				'num_edges': to_json(obj.num_edges)}
	raise TypeError(repr(obj) + ' is not JSON serializable')


def from_json(obj):
	if not isinstance(obj, dict):
		return obj
	
	if '__class__' in obj:
		if obj['__class__'] == 'Config':
			cfg = Config()
			cfg.num_models_to_generate = obj['num_models_to_generate']
			cfg.model_name = obj['model_name_prefix']
			cfg.num_state_machines = from_json(obj['num_state_machines'])
			cfg.statement_size = from_json(obj['statement_size'])
			cfg.sm_gen_method = from_json(obj['sm_gen_method'])
			cfg.num_vars_shared_by_more_than_two_sms = from_json(obj['num_vars_shared_by_more_than_two_sms'])
			return cfg
		elif obj['__class__'] == 'MinMax':
			return MinMax(obj['min'], obj['max'])
		elif obj['__class__'] == 'GraphGeneratorMixed':
			gen = GraphGeneratorMixed()
			gen.gen_list = from_json(obj['generator_list'])
			return gen
		elif obj['__class__'] == 'GraphGenerator_Erdos_Renyi':
			gen = GraphGenerator_Erdos_Renyi()
			gen.edge_probability = from_json(obj['edge_probability'])
			gen.num_nodes = from_json(obj['num_nodes'])
			return gen
		elif obj['__class__'] == 'GraphGenerator_Static_Power_Law':
			gen = GraphGenerator_Static_Power_Law()
			gen.num_nodes = from_json(obj['num_nodes'])
			gen.num_edges = from_json(obj['num_edges'])
			gen.exponent_out = from_json(obj['exponent_out'])
			gen.exponent_in  = from_json(obj['exponent_in'])
			return gen
		elif obj['__class__'] == 'GraphGenerator_SCC':
			gen = GraphGenerator_SCC()
			gen.degree_range = from_json(obj['degree_range'])
			gen.num_nodes = from_json(obj['num_nodes'])
			gen.num_edges = from_json(obj['num_edges'])
			return gen
	return obj
	

slco_template = """model %s {
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


statemachine = '''%s {
				variables
					%s
				initial %s
				states  %s
				transitions
					%s
				} '''

def make_graph_connected(g):
	g.vs['id'] = range(0, g.vcount())
	vertex_clustering = g.components(igraph.WEAK)
	components = vertex_clustering.subgraphs()
	if len(components) > 0:
		vertices = []
		for comp in components:
			vertices.append(comp.vs[0]['id'])
		edges = [(vertices[len(vertices) - 1], vertices[0])]
		for i in range(1, len(vertices)):
			edges.append((vertices[i - 1], vertices[i]))
		g.add_edges(edges)
	return g


def rand_exp_cap(lambd, min, max):
	n = random.expovariate(lambd)
	if n < min:
		n = min
	elif n > max:
		n = max
	return n


# n the number of state machines in the network
def generate_network_topology(n, mean):
	if mean < 2:
		mean = 2
	lambd = math.log(2)/(mean - 2) # minimum is 2 so we generate numbers from 0 to inf, then add 2
	out_degree = []
	sum = 0
	for i in range(1, n - 1):
		d = rand_exp_cap(lambd, 0, n - 1)
		sum += d
		out_degree.append(d)
	# make sum of degrees even
	d = rand_exp_cap(lambd, 0, n - 1)
	if sum % 2 != d % 2:
		d += 1
		if (d > n-1):
			d -= 2
	out_degree.append(d)
	return igraph.Graph.Degree_Sequence(out_degree, method="vl")


def make_statement(vars, var, chance_for_local):
	read = random.choice([True, False])
	write = random.choice([True, False])
	if not write:
		read = True
	if write:
		write_var = var
	else:
		write_var = local_var_idx if (random.uniform > chance_for_local) else random.choice(vars)
	if read:
		read_var = var
	else:
		read_var = local_var_idx if (random.uniform > chance_for_local) else random.choice(vars)
	return "var_%s := %s" % (write_var, read_var)


local_var_chance = 0.5


def generate_statement(vars):
	var = random.choice(vars)
	return make_statement(vars, var, local_var_chance)


def add_generated_statements(g, vars, statement_size):
	for e in range(0, g.ecount()):
		size = statement_size.randint()
		statement = ""
		# TODO: generate statements for all vars first!
		for i in range(0, size):
			statement += generate_statement(vars)
		if size > 1:
			statement = "[%s]" % statement
		g.es[e]["statement"] = statement
	return g


def generate_model(config, name):
	num_sm = config.num_state_machines.randint()
	sm_network = generate_network_topology(num_sm)
	# assign a variable to each edge (to be shared by two state machines)
	for i in range(0,sm_network.ecount()):
		sm_network.es[i]["vars"] = [i]
	# randomly generate a number of variables shared by more than two state machines
	max_shared_vars = min(num_sm - 1, config.num_vars_shared_by_more_than_two_sms.max)
	num_shared_vars = random.randint(config.num_vars_shared_by_more_than_two_sms.min, max_shared_vars)
	var_count = sm_network.ecount()
	for i in range(0, num_shared_vars):
		var_count += 1
		num_shared = random.randint(2, num_sm-1)
		selected_edges = set()
		while len(selected_edges) < num_shared:
			edge = random.randint(0, sm_network.ecount())
			if edge not in selected_edges:
				selected_edges.add(edge)
				sm_network.es[edge]["vars"].append(var_count)
	
	state_machines = []
	for i in range(0,num_sm):
		connected, g = config.sm_gen_method.generate()
		
		# if the graph is not connected, make it connected
		if not connected:
			g = make_graph_connected(g)
		# the graph is now connected
		vars = [e["vars"] for e in sm_network.incidents[i]]
		flat_vars = [item for sublist in vars for item in sublist]
		g = add_generated_statements(g, flat_vars, config.statement_size)
		state_machines.append(graph_to_slco(g))
	
	vars_text = vars[0] + "\n"
	for i in range(1,num_vars):
		vars_text += "\t\t\t%s\n" % vars[i]
		
	sm_text = state_machines[0] + "\n\n"
	for i in range(1, num_vars):
		sm_text += "\t\t\t%s\n\n" % state_machines[i]
		
	return slco_template % (name, vars, sm_text)
	
	
def generate_models(config, gen_folder):
	for i in range(0, config.num_models_to_generate):
		name = config.model_name + str(i)
		outFile = open(join(gen_folder, name + ".slco"), 'w')
		out_model = generate_model(config, name)
		outFile.write(out_model)
		outFile.close()


def main(args):
	"""The main function"""
	global slco_mm
	if len(args) > 0:
		if args[0] == '-h' or args[0] == '-help':
			print("Usage: pypy/python3 generator <config_file>")
			print("")
			print("Generate an SLCO 2.0 model.")
			sys.exit(0)
		
	config_file = args[0]
	config = Config.fromFile(config_file)
	
	gen_dir = "generated_slco"
	gen_folder = join(this_folder,gen_dir)
	if not exists(gen_folder):
		mkdir(gen_folder)
		
	generate_models(config, gen_folder)


if __name__ == '__main__':
	args = []
	for i in range(1,len(sys.argv)):
		args.append(sys.argv[i])
	main(args)

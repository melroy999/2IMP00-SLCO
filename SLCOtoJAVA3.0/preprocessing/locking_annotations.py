from rendering.model_rendering import get_instruction


def gather_used_variables(model, variables):
    """Gather the variables that are used within the statements"""
    class_name = model.__class__.__name__
    if class_name in ["Assignment", "Expression", "ExprPrec1", "ExprPrec2", "ExprPrec3", "ExprPrec4"]:
        gather_used_variables(model.left, variables)
        if model.right is not None:
            gather_used_variables(model.right, variables)
    elif class_name == "ExpressionRef":
        if model.index is None:
            variables.update({(model.ref, None)})
        else:
            # The index might hide a variable within it.
            variables.update({(model.ref, get_instruction(model.index))})
            gather_used_variables(model.index, variables)
    elif class_name == "VariableRef":
        if model.index is None:
            variables.update({(model.var.name, None)})
        else:
            # The index might hide a variable within it.
            variables.update({(model.var.name, get_instruction(model.index))})
            gather_used_variables(model.index, variables)
    elif class_name == "Primary" and model.ref is not None:
        return gather_used_variables(model.ref, variables)
    else:
        return set([])


def annotate_used_variables(o, global_variables=None):
    """"Add the used variables to Composites, Expressions and Assignments."""
    class_name = o.__class__.__name__
    if class_name == "Class":
        for sm in o.statemachines:
            annotate_used_variables(sm, global_variables)
    if class_name == "StateMachine":
        for transition in o.transitions:
            annotate_used_variables(transition, global_variables)
    elif class_name == "Transition":
        o.variables = set([])
        o.lock_requests = set([])
        for statement in o.statements:
            annotate_used_variables(statement, global_variables)
            o.variables.update(statement.variables)
            o.lock_requests.update(statement.lock_requests)
    elif class_name == "Composite":
        o.variables = set([])
        o.lock_requests = set([])
        for statement in [o.guard] + o.assignments:
            annotate_used_variables(statement, global_variables)
            o.variables.update(statement.variables)
            o.lock_requests.update(statement.lock_requests)
    elif class_name in ["Expression", "Assignment"]:
        o.variables = set([])
        gather_used_variables(o, o.variables)
        o.lock_requests = set([(name, sub) for name, sub in o.variables if name in global_variables])


class Node:
    """A simple node class used in the adjacency graph"""
    def __init__(self, key):
        self.predecessors = set([])
        self.successors = set([])
        self.key = key
        self.max_no_successors = 0
        self.max_no_predecessors = 0

    def __repr__(self):
        in_string = ",".join([v.key for v in self.predecessors])
        out_string = ",".join([v.key for v in self.successors])
        return "%s (in [%s], out [%s])" % (self.key, in_string, out_string)

    def add_successor(self, value):
        self.successors.add(value)
        self.max_no_successors = len(self.successors)
        value.predecessors.add(self)
        value.max_no_successors = len(value.predecessors)

    def remove_successor(self, value):
        self.successors.discard(value)
        value.predecessors.discard(self)

    def remove_predecessor(self, value):
        self.predecessors.discard(value)
        value.successors.discard(self)


def construct_variable_dependency_graph(o, variable_to_node, target_variables, variable_stack):
    """Construct a variable dependency graph, where a variable depends on another if it is used in the index"""
    # We require a variable stack on which the top item is the most recently encountered variable.
    if variable_stack is None:
        variable_stack = []
    if o is None:
        return

    class_name = o.__class__.__name__
    if class_name == "Transition":
        for s in o.statements:
            construct_variable_dependency_graph(s, variable_to_node, target_variables, variable_stack)
    elif class_name == "Composite":
        construct_variable_dependency_graph(o.guard, variable_to_node, target_variables, variable_stack)
        for a in o.assignments:
            construct_variable_dependency_graph(a, variable_to_node, target_variables, variable_stack)
    elif class_name == "ExpressionRef":
        if o.ref in target_variables:
            target_variable = variable_to_node.setdefault(o.ref, Node(o.ref))
            if len(variable_stack) > 0:
                parent_variable = variable_to_node.setdefault(variable_stack[-1], Node(variable_stack[-1]))
                parent_variable.add_successor(target_variable)
            variable_stack.append(o.ref)
        construct_variable_dependency_graph(o.index, variable_to_node, target_variables, variable_stack)
        if o.ref in target_variables:
            variable_stack.pop()
    elif class_name == "VariableRef":
        if o.var.name in target_variables:
            target_variable = variable_to_node.setdefault(o.var.name, Node(o.var.name))
            if len(variable_stack) > 0:
                parent_variable = variable_to_node.setdefault(variable_stack[-1], Node(variable_stack[-1]))
                parent_variable.add_successor(target_variable)
            variable_stack.append(o.var.name)
        construct_variable_dependency_graph(o.index, variable_to_node, target_variables, variable_stack)
        if o.var.name in target_variables:
            variable_stack.pop()
    elif class_name == "Primary":
        construct_variable_dependency_graph(o.body, variable_to_node, target_variables, variable_stack)
        construct_variable_dependency_graph(o.ref, variable_to_node, target_variables, variable_stack)
        construct_variable_dependency_graph(o.value, variable_to_node, target_variables, variable_stack)
    elif class_name in ["Assignment", "Expression", "ExprPrec1", "ExprPrec2", "ExprPrec3", "ExprPrec4"]:
        construct_variable_dependency_graph(o.left, variable_to_node, target_variables, variable_stack)
        construct_variable_dependency_graph(o.right, variable_to_node, target_variables, variable_stack)
    pass


def assign_lock_ids_to_class_variables(c):
    """Assign lock ids to every class variable, using a dependency graph"""
    # First, create nodes for every variable we are interested in.
    variable_to_node = {}
    for v in c.variables:
        v.lock_id = None

    # Create a dependency graph, where a variable x depends on y if it is used in the index of x.
    for sm in c.statemachines:
        for t in sm.transitions:
            target_variables = set(c.name_to_variable.keys())
            construct_variable_dependency_graph(t, variable_to_node, target_variables, [])

    # Assign lock identities.
    unassigned = set(variable_to_node.keys())
    current_lock_id = 0
    while len(unassigned) > 0:
        # Start assigning lock ids, starting with the nodes that have no dependencies.
        # Repeat this until no variables are found that have no dependencies.
        while any(len(variable_to_node[v].successors) == 0 for v in unassigned):
            for v in [v for v in unassigned if len(variable_to_node[v].successors) == 0]:
                target_node = variable_to_node[v]
                variable = c.name_to_variable[v]
                variable.lock_id = current_lock_id
                unassigned.discard(v)

                # Remove the association of the predecessor nodes to the target node.
                for node in target_node.predecessors:
                    node.successors.discard(target_node)

                # Determine the next id to use.
                current_lock_id += variable.type.size if variable.type.size > 1 else 1

        # Sort the list of unassigned variables on number of dependencies.
        sorted_unassigned = sorted(list(unassigned), key=lambda _v: (variable_to_node[_v].max_no_successors, _v))

        # No more leaves can be found, which implies that circular references exist in the dependency graph.
        # Process the node that depends on the fewest other nodes.
        if len(sorted_unassigned) > 0:
            v = sorted_unassigned[0]
            target_node = variable_to_node[v]
            variable = c.name_to_variable[v]
            variable.lock_id = current_lock_id
            unassigned.discard(v)

            # Remove any existing self-references.
            target_node.predecessors.discard(target_node)

            # Remove the association of the predecessor nodes to the target node.
            for node in target_node.predecessors:
                node.successors.discard(target_node)
                node.predecessors.discard(target_node)

            # Determine the next id to use.
            current_lock_id += variable.type.size if variable.type.size > 1 else 1

    # Set metadata for the number of locks in the class.
    c.number_of_locks = current_lock_id

    # Print a report.
    print_locking_report(c)


def get_lock_id_ordering(o, name_to_variable):
    """Get the lock id of the given variable, used for sorting purposes"""
    v, i = o
    try:
        # Check if the index is a simple string or a variable.
        offset = int(i)
    except (ValueError, TypeError):
        # If it is a variable, fall back to no offset.
        offset = 0
    return name_to_variable[v].lock_id + offset


def correct_dependency_graph(variable_dependency_graph, name_to_variable, lock_requests):
    """Remove all dependencies that violate the lock id ordering, and decompose array lock requests when appropriate."""
    # If a node has a dependency on a higher id node, remove all dependencies of the node.
    # Remove superfluous lock id statements--all original lock id statements starting with the variable are superfluous.
    for node in variable_dependency_graph.values():
        target_variable = name_to_variable[node.key]

        # Check if the lock id of one of the dependants is higher than the current target node.
        if any(name_to_variable[v.key].lock_id >= target_variable.lock_id for v in node.successors):
            # Remove all lock id requests for the currently targeted variable.
            lock_requests.symmetric_difference_update(set((v, i) for v, i in lock_requests if v == node.key))

            # Create lock ids for all values of the variable associated to the node.
            lock_requests.update((node.key, i) for i in range(0, target_variable.type.size))

            # Remove all dependencies of the node after having made the corrections.
            for successor_node in list(node.successors):
                node.remove_successor(successor_node)


def get_locking_phases(variable_dependency_graph, name_to_variable, lock_requests):
    """Convert the list of lock ids to locking phases, adhering to the given dependency graph"""
    # The assumption here is that the dependency graph has been preprocessed to no longer have circular dependencies.
    lock_id_ordering = sorted(lock_requests, key=lambda _v: get_lock_id_ordering(_v, name_to_variable))
    lock_phases = []
    current_phase = []
    encountered_nodes = set([])

    # Iterate over all locking requests found in the lock id list and procedurally add them to phases.
    for v, i in lock_id_ordering:
        # Find the node associated with the variable.
        target_node = variable_dependency_graph[v]

        # If the node has any successors, we need to move on to the next phase.
        if len(target_node.successors) > 0:
            # Flush the current phase.
            lock_phases.append(current_phase)
            current_phase = []

            # Remove all nodes in the flushed phase from the graph.
            for node in encountered_nodes:
                for predecessor_node in list(node.predecessors):
                    node.remove_predecessor(predecessor_node)

        # Add the variable and index to the current phase.
        current_phase.append((v, i))
        encountered_nodes.add(target_node)

    # Flush the last phase, if it is non-empty.
    if len(current_phase) > 0:
        lock_phases.append(current_phase)
    return lock_phases


def annotate_lock_phases(o, name_to_variable):
    """Create locking phases for the given statement"""
    # Construct a variable dependency graph for the statement.
    variable_dependency_graph = {}
    construct_variable_dependency_graph(o, variable_dependency_graph, set(name_to_variable.keys()), [])

    # Correct the dependency graph by expanding nodes that will violate the lock identity ordering.
    correct_dependency_graph(variable_dependency_graph, name_to_variable, o.lock_requests)

    # Break the lock id list into different phases, following the dependency graph.
    o.lock_request_phases = get_locking_phases(variable_dependency_graph, name_to_variable, o.lock_requests)


def annotate_lock_list(c):
    """Construct a phased lock ordering for all transitions in the given class"""
    for sm in c.statemachines:
        for t in sm.transitions:
            for s in t.statements:
                annotate_lock_phases(s, c.name_to_variable)


def print_locking_report(c):
    """Print a formatted report of the locks of a given class"""
    print("#" * 120)
    print("Class: %s" % c.name)
    print()
    print("Assigned lock identities:")
    for v in sorted(c.variables, key=lambda _v: _v.lock_id):
        assigned_locks = [str(v.lock_id + i) for i in range(max(1, v.type.size))]
        print("\t- %s: [%s]" % (v.name, ",".join(assigned_locks)))

    print("#" * 120)
    print()

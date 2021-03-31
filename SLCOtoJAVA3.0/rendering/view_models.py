import copy

from z3 import z3

import settings
from preprocessing.locking_annotations import correct_dependency_graph, construct_variable_dependency_graph, \
    get_locking_phases, get_lock_request_ranges
from util.to_java import get_java_type, get_initial_value, get_default_value
from util.z3py import z3_check_trivially_satisfiable


def get_variable_instantiation_list(model, variables):
    """Construct a comma separated list of variable initializations sorted on by name"""
    # The initialization of class variables are processed per initialization.
    instantiated_variables = {
        _v.left.name: _v.rights if _v.right is None else _v.right for _v in model
    }

    variable_instantiations = []
    for v in sorted(variables, key=lambda o: o.name):
        # Is a value assigned to the variable? If so, use it, otherwise, fall back to the default.
        value = instantiated_variables[v.name] if v.name in instantiated_variables else get_default_value(v)

        # Convert the variable to the Java representation.
        value = "{%s}" % ", ".join(str(v).lower() for v in value) if isinstance(value, list) else str(value).lower()

        if v.type.size > 1:
            variable_instantiations.append("new %s %s" % (get_java_type(v.type, False), value))
        else:
            variable_instantiations.append("%s" % value)

    return variable_instantiations


class ModelBlock:
    """A view model for the SLCO model"""
    def __init__(self, model):
        # The classes in the model.
        self.classes = [ClassBlock(c) for c in model.classes]

        # The name of the model.
        self.name = model.name

        # Do any of the state machines require locking functionality?
        self.include_lock_manager = any(c.has_class_variables for c in self.classes)

        # Are locks supposed to be fair?
        self.lock_fairness = settings.lock_fairness


def get_variable_list(model):
    """Construct a comma separated list of variables, sorted on by name and prefixed with their type"""
    variables = ["%s %s" % (get_java_type(_v.type, False), _v.name) for _v in sorted(model, key=lambda v: v.name)]
    return ", ".join(variables)


class ClassBlock:
    """A view model for a class"""
    def __init__(self, c):
        # The state machines in the class.
        self.state_machines = [StateMachineBlock(sm) for sm in c.statemachines]

        # The name of the class.
        self.name = c.name

        # The name of the model.
        self.model_name = c.parent.name

        # Which variables are in the model?
        self.variables = c.variables

        # Which variable declarations need to be rendered?
        self.variable_declarations = []
        for v in sorted(c.variables, key=lambda _v: _v.lock_id):
            self.variable_declarations.append(
                "private %s %s %s;%s" % (
                    "volatile" if v.type.size < 1 else "final",
                    get_java_type(v.type),
                    v.name,
                    " // Lock id %s" % v.lock_id if v.lock_id is not None else ""
                )
            )

        # Which variable instantiations need to be rendered?
        self.variable_instantiations = ["this.%s = %s;" % (v.name, v.name) for v in c.variables]

        # The list of variables that needs to be included in the constructor.
        self.constructor_variable_list = get_variable_list(c.variables)

        # Does the class need to lock?
        self.has_class_variables = len(c.variables) > 0

        # The number of locks present in the model, if available.
        self.number_of_locks = c.number_of_locks

        # Which state machines need to be declared?
        self.state_machine_declarations = [
            "private final %sThread T_%s;" % (sm.name, sm.name) for sm in self.state_machines
        ]

        # Which state machines need to be instantiated?
        self.state_machine_instantiations = [
            "T_%s = new %s.%sThread(%s);" % (
                sm.name,
                self.name,
                sm.name,
                "lockManager" if sm.uses_class_variables else ""
            ) for sm in self.state_machines
        ]

        # Which variable lists do we have for the instantiations of classes?
        self.variable_lists_for_class_instantiations = [
            get_variable_instantiation_list(o.assignments, c.variables) for o in c.objects
        ]


def has_non_deterministic_block(tree):
    """Check whether the given tree object has a non-deterministic block within it"""
    class_name = tree.__class__.__name__
    if class_name in ["TransitionBlock", "NoneType"]:
        return False
    elif class_name == "NonDeterministicBlock":
        return True
    else:
        return any(has_non_deterministic_block(node) for node in tree.choice_blocks)


class StateMachineBlock:
    """A view model for a state machine"""
    def __init__(self, sm):
        # The states in the state machine.
        self.states = sm.states

        # The initial state of the state machine.
        self.initial_state = sm.initial_state

        # Does the state machine require a current state variable?
        self.render_current_state_variable = len(sm.states) > 1

        # The name of the state machine, the parent class, and parent model.
        self.name = sm.name
        self.class_name = sm.parent_class.name
        self.model_name = sm.parent_class.parent.name

        # A reference to the parent class for variable resolving.
        self.parent_class = sm.parent_class

        # Is the number of transitions the state machine can make limited?
        self.add_transition_limit = settings.add_counter
        self.max_nr_of_iterations = settings.max_nr_of_iterations
        self.add_time_limit = settings.add_timer
        self.max_running_time = settings.max_running_time

        # Are we measuring performance?
        self.add_performance_counters = settings.add_performance_counter

        # Which variable declarations need to be rendered?
        self.variable_instantiations = []
        for v in sm.variables:
            if v.type.size < 1:
                # Normal variable.
                self.variable_instantiations.append(
                    "private %s %s = %s;" % (
                        get_java_type(v.type),
                        v.name,
                        get_initial_value(v)
                    )
                )
            else:
                # Array variable.
                self.variable_instantiations.append(
                    "private final %s %s = new %s%s;" % (
                        get_java_type(v.type),
                        v.name,
                        get_java_type(v.type),
                        get_initial_value(v)
                    )
                )

        # The groupings per state.
        self.groupings = {state: get_view_model(grouping, sm.parent_class) for state, grouping in sm.groupings.items()}

        # Does the state machine have non-deterministic choices?
        self.has_non_determinism = any(has_non_deterministic_block(grouping) for grouping in self.groupings.values())

        # Does the state machine use class variables?
        self.uses_class_variables = len(sm.lock_requests) > 0

        # The number of locks ids to reserve.
        self.total_nr_of_unique_locks = sm.total_nr_of_unique_locks


class NonDeterministicBlock:
    """A wrapper for a non-deterministic choice"""
    def __init__(self, choice_blocks):
        # Define the choice blocks contained by this construct.
        self.choice_blocks = choice_blocks

        # Which lock requests are present within the child blocks?
        self.lock_requests = set([])

        # What is the resulting encapsulating guard expression?
        self.guard_expressions = set([])
        self.guard_statements = set([])
        for block in choice_blocks:
            self.lock_requests.update(block.lock_requests)
            if block.__class__.__name__ == "TransitionBlock":
                self.guard_expressions.add(block.guard_expression)
                self.guard_statements.add(block.guard_statement)
            else:
                self.guard_expressions |= block.guard_expressions
                self.guard_statements |= block.guard_statements


class DeterministicIfThenElseBlock:
    """A wrapper for a simple deterministic if-then-else block"""
    def __init__(self, choice_blocks):
        # Define the choice blocks contained by this construct.
        self.choice_blocks = choice_blocks

        # Which lock requests are present within the child blocks?
        self.lock_requests = set([])

        # Do we require to lock certain variables?
        self.render_acquire_locks = False

        # If so, which lock request phases do we have, and what are the lock ranges that need to be acquired?
        self.lock_request_phases = []
        self.lock_ranges = []

        # In case of no else, locks have to be released.
        self.render_release_locks = False

        # Up to which lock entry in the lock list do we need to release?
        self.release_up_to_lock = 0

        # What is the resulting encapsulating guard expression?
        self.guard_expressions = set([])
        self.guard_statements = set([])
        for block in choice_blocks:
            self.lock_requests.update(block.lock_requests)
            if block.__class__.__name__ == "TransitionBlock":
                self.guard_expressions.add(block.guard_expression)
                self.guard_statements.add(block.guard_statement)
            else:
                self.guard_expressions |= block.guard_expressions
                self.guard_statements |= block.guard_statements

        # Does the combination of all the guards always evaluate to true? If so, we can use an else statement.
        self.close_with_else = False
        encapsulating_guard_expression = z3.Or([e.z3py_expression for e in self.guard_expressions])
        if len(self.guard_expressions) > 0 and z3_check_trivially_satisfiable(encapsulating_guard_expression):
            self.close_with_else = True

        # Disable the guards of child transition blocks.
        for block in choice_blocks:
            if block.__class__.__name__ == "TransitionBlock":
                block.encompass_transition_guard(False)
            elif block.__class__.__name__ == "NonDeterministicBlock":
                # Note that we might have multiple statements with the same guard in a nested non deterministic block.
                # TODO ensure that guard expressions are only removed when safe!
                for nested_block in block.choice_blocks:
                    if nested_block.__class__.__name__ == "TransitionBlock":
                        # The transition doesn't need a guard if the encompassing guard only contains one element.
                        nested_block.encompass_transition_guard(len(block.guard_expressions) > 1)


class TransitionBlock:
    """A wrapper for a transition leaf in the decision tree"""
    def __init__(self, t):
        self.guard_expression = t.guard_expression
        self.guard_statement = t.guard
        self.target = t.target
        self.always_fails = False

        # Remove expressions that are unreachable.
        statements = t.statements
        for i in range(0, len(statements)):
            statement = statements[i]
            if statement.__class__.__name__ == "Expression" and statement.is_trivially_unsatisfiable:
                self.always_fails = True
                statements = statements[:i]
                break

        # Create
        self.statements = [construct_view_model(s) for s in statements]

        # Which traceability comment would we like to add?
        self.comment = t.comment_string

        # Which locks do we aim to acquire?
        self.lock_requests = t.guard.lock_requests

    def encompass_transition_guard(self, render_guard):
        """Disable the rendering of the guard expression."""
        if len(self.statements) > 0:
            self.statements[0].encompass_transition_guard(render_guard)

    def set_number_of_locks_to_release(self, n):
        if len(self.statements) > 0:
            self.statements[0].set_number_of_locks_to_release(n)

    def __repr__(self):
        return self.guard_expression.__repr__()


# Operators that can be negated.
operator_to_negation = {
    ">": "<=",
    ">=": "<",
    "<": ">=",
    "<=": ">",
    "=": "!=",
    "!=": "=",
    "<>": "=",
}


def recursively_negate_expression(o):
    class_name = o.__class__.__name__
    if class_name in ["Expression", "ExprPrec1", "ExprPrec2", "ExprPrec3", "ExprPrec4"]:
        if o.op == "":
            result, expression = recursively_negate_expression(o.left)
            if result:
                c = copy.copy(o)
                c.left = expression
                return result, c
            else:
                return result, expression
        else:
            if o.op in operator_to_negation:
                # Negate by changing the operator to its complement.
                c = copy.copy(o)
                c.op = operator_to_negation[o.op]
                return True, c
            else:
                # Can't negate.
                return False, None
    elif class_name == "Primary":
        if o.sign == "Not":
            return False, o.body
        else:
            return False, None
    else:
        return False, None


def negate_expression(expression):
    """Wrap the given expression with a not statement"""
    result, negation = recursively_negate_expression(expression)
    if result:
        # An altered version of the original formula is given.
        return negation
    else:
        if negation:
            # A subtree of the AST is given as a negation.
            return negation
        else:
            # Could not negate, so add a not.
            return type("Expression", (object,), {
                "left": type("Primary", (object,), {"value": None, "sign": "not", "body": expression, "ref": None})(),
                "op": "",
                "right": None
            })()


class ExpressionBlock:
    """A wrapper for expressions in a transition"""
    def __init__(self, expression):
        # Does the expression need to be rendered?
        self.render_expression = not expression.is_trivially_satisfiable

        # What is the expression that needs to be rendered?
        self.expression_negation = negate_expression(expression)

        # Do we require to lock certain variables?
        self.render_acquire_locks = len(expression.lock_request_phases) > 0

        # If so, which lock request phases do we have, and what are the lock ranges that need to be acquired?
        self.lock_request_phases = expression.lock_request_phases
        self.lock_ranges = expression.lock_ranges

        # Which locks do we aim to acquire?
        self.lock_requests = expression.lock_requests

        # Do we require to lock certain variables?
        self.render_release_locks = len(expression.lock_request_phases) > 0

        # Up to which lock entry in the lock list do we need to release?
        self.release_up_to_lock = len(expression.lock_requests)

    def encompass_transition_guard(self, render_guard):
        self.render_expression = render_guard
        self.render_acquire_locks = False
        self.render_release_locks = False

    def set_number_of_locks_to_release(self, n):
        self.render_release_locks = True
        self.release_up_to_lock = n

    def __repr__(self):
        return self.expression_negation.__repr__()


class AssignmentBlock:
    """A wrapper for assignments in a transition"""
    def __init__(self, assignment):
        # What is the assignment that needs to be rendered?
        self.assignment = assignment

        # Do we require to lock certain variables?
        self.render_acquire_locks = len(assignment.lock_request_phases) > 0

        # If so, which lock request phases do we have, and what are the lock ranges that need to be acquired?
        self.lock_request_phases = assignment.lock_request_phases
        self.lock_ranges = assignment.lock_ranges

        # Which locks do we aim to acquire?
        self.lock_requests = assignment.lock_requests

        # Do we require to lock certain variables?
        self.render_release_locks = len(assignment.lock_request_phases) > 0

        # Up to which lock entry in the lock list do we need to release?
        self.release_up_to_lock = len(assignment.lock_requests)

    def encompass_transition_guard(self, render_guard):
        pass

    def set_number_of_locks_to_release(self, n):
        pass

    def __repr__(self):
        return self.assignment.__repr__()


class CompositeBlock:
    """A wrapper for composites in a transition"""
    def __init__(self, composite):
        # Does the guard of the composite need to be rendered?
        self.render_guard = not composite.guard.is_trivially_satisfiable

        # What is the composite we are rendering?
        self.composite = composite

        # What is the guard that needs to be rendered?
        self.guard_negation = negate_expression(composite.guard)

        # What are the statements that need to be rendered?
        self.assignments = composite.assignments

        # Do we require to lock certain variables?
        self.render_acquire_locks = len(composite.lock_request_phases) > 0

        # If so, which lock request phases do we have, and what are the lock ranges that need to be acquired?
        self.lock_request_phases = composite.lock_request_phases
        self.lock_ranges = composite.lock_ranges

        # Which locks do we aim to acquire?
        self.lock_requests = composite.lock_requests

        # Do we require to lock certain variables?
        self.render_release_locks = len(composite.lock_request_phases) > 0

        # Up to which lock entry in the lock list do we need to release?
        self.release_up_to_lock = len(composite.lock_requests)

    def encompass_transition_guard(self, render_guard):
        self.render_guard = render_guard
        self.render_acquire_locks = False
        self.render_release_locks = False

    def set_number_of_locks_to_release(self, n):
        self.render_release_locks = True
        self.release_up_to_lock = n

    def __repr__(self):
        return self.composite.__repr__()


def construct_view_model(node):
    """Convert the decision structure to view models"""
    class_name = node.__class__.__name__
    if class_name == "Expression":
        return ExpressionBlock(node)
    if class_name == "Assignment":
        return AssignmentBlock(node)
    if class_name == "Composite":
        return CompositeBlock(node)
    elif class_name == "Transition":
        return TransitionBlock(node)
    else:
        # Get the choice type and the choices made in this decision node.
        choice_type, children = node

        if choice_type.value == 1:
            return NonDeterministicBlock([construct_view_model(sub_node) for sub_node in children])
        else:
            # Determine which types of deterministic blocks to use for the child nodes.
            choice_blocks = [construct_view_model(_c) for _c in children]
            return DeterministicIfThenElseBlock(choice_blocks)


def propagate_acquire_locks(model, name_to_variable):
    """Propagate the locks to acquire over the choice block view models"""
    model_class = model.__class__.__name__
    if model_class == "NonDeterministicBlock":
        # Locking is done exclusively in decision blocks.
        for block in model.choice_blocks:
            propagate_acquire_locks(block, name_to_variable)
    elif model_class != "TransitionBlock":
        # We always acquire the locks at the soonest convenience--further recursion is unnecessary.
        # Make sure that we acquire the locks in the desired phases.
        dependency_graph = {}
        for expression in model.guard_statements:
            construct_variable_dependency_graph(expression, dependency_graph, set(name_to_variable.keys()), [])

        # If a node has a dependency on a higher id node, expand and remove all dependencies of the node.
        correct_dependency_graph(dependency_graph, name_to_variable, None)

        # Break the lock id list into different phases, following the dependency graph.
        model.lock_request_phases = get_locking_phases(dependency_graph, name_to_variable, model.lock_requests)
        model.lock_ranges = get_lock_request_ranges(model)
        model.render_acquire_locks = True

        # Ensure that locks are released in empty branches.
        model.release_up_to_lock = len(model.lock_requests)
        model.render_release_locks = True


def propagate_release_locks(model, parent_lock_requests=None):
    """Propagate the locks to release over the choice block view models"""
    if parent_lock_requests is None:
        parent_lock_requests = set([])
    model_class = model.__class__.__name__
    if model_class == "TransitionBlock":
        # Set the number of locks that have to be released.
        if len(parent_lock_requests) > 0:
            model.set_number_of_locks_to_release(len(parent_lock_requests))
    elif model_class == "NonDeterministicBlock":
        for block in model.choice_blocks:
            propagate_release_locks(block, parent_lock_requests)
    elif model_class == "DeterministicCaseDistinctionBlock":
        lock_requests = parent_lock_requests | model.lock_requests
        for _, block in model.choice_blocks:
            propagate_release_locks(block, lock_requests)
        if model.default_decision_tree:
            propagate_release_locks(model.default_decision_tree, lock_requests)
    elif model_class == "DeterministicIfThenElseBlock":
        lock_requests = parent_lock_requests | model.lock_requests
        for block in model.choice_blocks:
            propagate_release_locks(block, lock_requests)


def get_view_model(node, c):
    if node is None:
        return

    """Get a view model for the given decision structure and add the appropriate locking tags"""
    decision_tree = construct_view_model(node)

    # Ensure that the acquire lock tags are set correctly.
    propagate_acquire_locks(decision_tree, c.name_to_variable)
    propagate_release_locks(decision_tree)

    return decision_tree

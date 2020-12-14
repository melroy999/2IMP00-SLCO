from z3 import z3

from preprocessing.locking_annotations import correct_dependency_graph, construct_variable_dependency_graph, \
    get_locking_phases, get_lock_request_ranges
from util.z3py import z3_check_trivially_satisfiable


def wrap_in_not_expression(expression):
    """Wrap the given expression with a not statement"""
    return type("Expression", (object,), {
        "left": type("Primary", (object,), {"value": None, "sign": "not", "body": expression, "ref": None})(),
        "op": "",
        "right": None
    })()


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
                        nested_block.encompass_transition_guard(True)


class DeterministicCaseDistinctionBlock:
    """A wrapper for a deterministic case distinction block"""
    def __init__(self, subject_expression, choice_blocks, default_decision_tree):
        # Define the choice blocks contained by this construct.
        self.choice_blocks = choice_blocks
        self.subject_expression = subject_expression
        self.default_decision_tree = default_decision_tree

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

        # What is the encapsulating guard expression?
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
        if default_decision_tree is not None:
            self.lock_requests.update(default_decision_tree.lock_requests)
            if default_decision_tree.__class__.__name__ == "TransitionBlock":
                self.guard_expressions.add(default_decision_tree.guard_expression)
                self.guard_statements.add(default_decision_tree.guard_statement)
            else:
                self.guard_expressions |= default_decision_tree.guard_expressions
                self.guard_statements |= default_decision_tree.guard_statements


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


class ExpressionBlock:
    """A wrapper for expressions in a transition"""
    def __init__(self, expression):
        # Does the expression need to be rendered?
        self.render_expression = not expression.is_trivially_satisfiable

        # What is the expression that needs to be rendered?
        # TODO negate the formula prematurely and simplify using tree manipulations.
        self.expression_negation = wrap_in_not_expression(expression)

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
        # TODO negate the formula prematurely and simplify using tree manipulations.
        self.guard_negation = wrap_in_not_expression(composite.guard)

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
    """Convert the preprocessed decision tree to their associated view models"""
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
    decision_tree = construct_view_model(node)

    # Ensure that the acquire lock tags are set correctly.
    propagate_acquire_locks(decision_tree, c.name_to_variable)
    propagate_release_locks(decision_tree)

    return decision_tree

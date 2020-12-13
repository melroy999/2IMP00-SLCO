from z3 import z3

from util.z3py import z3_check_trivially_satisfiable


class NonDeterministicBlock:
    """A wrapper for a non-deterministic choice"""
    def __init__(self, choice_blocks):
        # Define the choice blocks contained by this construct.
        self.choice_blocks = choice_blocks

        # Which lock requests are present within the child blocks?
        self.lock_requests = set([])

        # What is the resulting encapsulating guard expression?
        self.guard_expressions = set([])
        for block in choice_blocks:
            self.lock_requests.update(block.lock_requests)
            if block.__class__.__name__ == "TransitionBlock":
                self.guard_expressions.add(block.guard_expression)
            else:
                self.guard_expressions |= block.guard_expressions


class DeterministicIfThenElseBlock:
    """A wrapper for a simple deterministic if-then-else block"""
    def __init__(self, choice_blocks):
        # Define the choice blocks contained by this construct.
        self.choice_blocks = choice_blocks

        # Which lock requests are present within the child blocks?
        self.lock_requests = set([])

        # What is the resulting encapsulating guard expression?
        self.guard_expressions = set([])
        for block in choice_blocks:
            self.lock_requests.update(block.lock_requests)
            if block.__class__.__name__ == "TransitionBlock":
                self.guard_expressions.add(block.guard_expression)
            else:
                self.guard_expressions |= block.guard_expressions

        # Does the combination of all the guards always evaluate to true? If so, we can use an else statement.
        self.close_with_else = False
        encapsulating_guard_expression = z3.Or([e.z3py_expression for e in self.guard_expressions])
        if len(self.guard_expressions) > 0 and z3_check_trivially_satisfiable(encapsulating_guard_expression):
            self.close_with_else = True

        # Disable the guards of child transition blocks.
        for block in choice_blocks:
            if block.__class__.__name__ == "TransitionBlock":
                block.deactivate_transition_guard()


class DeterministicCaseDistinctionBlock:
    """A wrapper for a deterministic case distinction block"""
    def __init__(self, subject_expression, choice_blocks, default_decision_tree):
        # Define the choice blocks contained by this construct.
        self.choice_blocks = choice_blocks
        self.subject_expression = subject_expression
        self.default_decision_tree = default_decision_tree

        # Which lock requests are present within the child blocks?
        self.lock_requests = set([])

        # What is the encapsulating guard expression?
        self.guard_expressions = set([])
        for block in choice_blocks:
            self.lock_requests.update(block.lock_requests)
            if block.__class__.__name__ == "TransitionBlock":
                self.guard_expressions.add(block.guard_expression)
            else:
                self.guard_expressions |= block.guard_expressions
        if default_decision_tree is not None:
            self.lock_requests.update(default_decision_tree.lock_requests)
            if default_decision_tree.__class__.__name__ == "TransitionBlock":
                self.guard_expressions.add(default_decision_tree.guard_expression)
            else:
                self.guard_expressions |= default_decision_tree.guard_expressions


class TransitionBlock:
    """A wrapper for a transition leaf in the decision tree"""
    def __init__(self, t):
        self.guard_expression = t.guard_expression
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

    def deactivate_transition_guard(self):
        """Disable the rendering of the guard expression."""
        if len(self.statements) > 0:
            self.statements[0].disable_guard()
            self.statements[0].disable_locks()

    def __repr__(self):
        return self.guard_expression.__repr__()


class ExpressionBlock:
    """A wrapper for expressions in a transition"""
    def __init__(self, expression):
        # Does the expression need to be rendered?
        self.render_expression = not expression.is_trivially_satisfiable

        # What is the expression that needs to be rendered?
        # TODO negate the formula prematurely and simplify using tree manipulations.
        self.expression = expression

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

    def disable_guard(self):
        self.render_expression = False

    def disable_locks(self):
        self.render_acquire_locks = False
        self.render_release_locks = False

    def __repr__(self):
        return self.expression.__repr__()


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

    def disable_guard(self):
        pass

    def disable_locks(self):
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
        self.guard = composite.guard

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

    def disable_guard(self):
        self.render_guard = False

    def disable_locks(self):
        self.render_acquire_locks = False
        self.render_release_locks = False

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


def get_view_model(node, c):
    return construct_view_model(node)

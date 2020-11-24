class NonDeterministicBlock:
    """A wrapper for a non-deterministic choice"""
    def __init__(self, choice_blocks):
        # Define the choice blocks contained by this construct.
        self.choice_blocks = choice_blocks

        # What is the encapsulating guard expression?
        self.encapsulating_guard_expression = set([])

        # Which statements are used as guards?
        self.encapsulating_guard_statements = set([])

        for block in choice_blocks:
            if block.__class__.__name__ == "TransitionBlock":
                self.encapsulating_guard_expression.add(block.guard_expression)
                self.encapsulating_guard_statements.add(block.guard)
            else:
                self.encapsulating_guard_expression |= block.encapsulating_guard_expression
                self.encapsulating_guard_statements |= block.encapsulating_guard_statements


class DeterministicIfThenElseBlock:
    """A wrapper for a simple deterministic if-then-else block"""
    def __init__(self, choice_blocks):
        # Define the choice blocks contained by this construct.
        self.choice_blocks = choice_blocks

        # What is the encapsulating guard expression?
        self.encapsulating_guard_expression = set([])

        # Which statements are used as guards?
        self.encapsulating_guard_statements = set([])

        for block in choice_blocks:
            if block.__class__.__name__ == "TransitionBlock":
                self.encapsulating_guard_expression.add(block.guard_expression)
                self.encapsulating_guard_statements.add(block.guard)
            else:
                self.encapsulating_guard_expression |= block.encapsulating_guard_expression
                self.encapsulating_guard_statements |= block.encapsulating_guard_statements


class DeterministicCaseDistinctionBlock:
    """A wrapper for a deterministic case distinction block"""
    def __init__(self, subject_expression, choice_blocks, default_decision_tree):
        # Define the choice blocks contained by this construct.
        self.choice_blocks = choice_blocks
        self.subject_expression = subject_expression
        self.default_decision_tree = default_decision_tree

        # What is the encapsulating guard expression?
        self.encapsulating_guard_expression = set([])

        # Which statements are used as guards?
        self.encapsulating_guard_statements = set([])

        for target, block in choice_blocks:
            if block.__class__.__name__ == "TransitionBlock":
                self.encapsulating_guard_expression.add(block.guard_expression)
                self.encapsulating_guard_statements.add(block.guard)
            else:
                self.encapsulating_guard_expression |= block.encapsulating_guard_expression
                self.encapsulating_guard_statements |= block.encapsulating_guard_statements

        if default_decision_tree is not None:
            if default_decision_tree.__class__.__name__ == "TransitionBlock":
                self.encapsulating_guard_expression.add(default_decision_tree.guard_expression)
                self.encapsulating_guard_statements.add(default_decision_tree.guard)
            else:
                self.encapsulating_guard_expression |= default_decision_tree.encapsulating_guard_expression
                self.encapsulating_guard_statements |= default_decision_tree.encapsulating_guard_statements


class TransitionBlock:
    """A wrapper for a transition leaf in the decision tree"""
    def __init__(self, t):
        self.guard = t.guard
        self.guard_expression = t.guard_expression
        self.statements = t.statements
        self.starts_with_composite = t.guard.__class__.__name__ == "Composite"
        self.composite_assignments = t.guard.assignments if self.starts_with_composite else None
        self.target = t.target
        self.always_fails = t.always_fails

        # Which traceability comment would we like to add?
        self.comment = t.comment_string

    def __repr__(self):
        return self.guard_expression.__repr__()


def construct_view_model(node):
    """Convert the preprocessed decision tree to their associated view models"""
    if node.__class__.__name__ == "Transition":
        # Create a transition block.
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

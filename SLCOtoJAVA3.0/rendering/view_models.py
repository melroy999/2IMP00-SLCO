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
        self.always_fails = t.always_fails

        # Remove expressions that are always true and remove statements that are unreachable.
        self.statements = [
            s for s in t.statements if s.__class__.__name__ != "Expression" or not s.is_trivially_satisfiable
        ]
        for i in range(0, len(self.statements)):
            statement = self.statements[i]
            if statement.__class__.__name__ == "Expression" and statement.is_trivially_unsatisfiable:
                self.always_fails = True
                self.statements = self.statements[:i]
                break

        # Which traceability comment would we like to add?
        self.comment = t.comment_string

        # Which locks do we aim to acquire?
        self.lock_requests = t.guard.lock_requests

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

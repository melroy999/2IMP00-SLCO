import operator
import z3

import settings
from util.z3py import z3_check_trivially_satisfiable, z3_check_trivially_unsatisfiable, z3_check_and
from enum import Enum

# Map every operator to its implementation to avoid calling eval.
operator_mapping = {
    ">": operator.gt,
    "<": operator.lt,
    ">=": operator.ge,
    "<=": operator.le,
    "=": operator.eq,
    "!=": operator.ne,
    "<>": operator.ne,
    "not": z3.Not,
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "**": operator.pow,
    "neg": operator.neg,
    "%": operator.mod,
    "/": operator.floordiv,
    "or": z3.Or,
    "||": z3.Or,
    "and": z3.And,
    "&&": z3.And,
    "xor": z3.Xor,
}


class Decision(Enum):
    """A simple enum that denotes whether a decision is made deterministically or non-deterministically"""
    DET = 0
    N_DET = 1

    def __repr__(self):
        return self.__str__()


def get_z3py_variable(v):
    """Convert the given variable object to a z3py variable"""
    if v.type.base == "Boolean":
        if v.type.size < 1:
            return z3.Bool(v.name)
        else:
            return z3.Array(v.name, z3.IntSort(), z3.BoolSort())
    else:
        if v.type.size < 1:
            return z3.Int(v.name)
        else:
            return z3.Array(v.name, z3.IntSort(), z3.IntSort())


def get_z3_operator_representation(op, *values):
    """Translate the given operator and the values to an evaluable object"""
    if len(values) == 1:
        return operator_mapping[op](values[0])
    else:
        return operator_mapping[op](values[0], values[1])


def textx_to_z3py_model(ast, variables):
    """Translate the given textx AST to z z3py model"""
    class_name = ast.__class__.__name__
    if class_name in ["Expression", "ExprPrec1", "ExprPrec2", "ExprPrec3", "ExprPrec4"]:
        if ast.right is None:
            return textx_to_z3py_model(ast.left, variables)
        else:
            return get_z3_operator_representation(
                ast.op, textx_to_z3py_model(ast.left, variables), textx_to_z3py_model(ast.right, variables)
            )
    elif class_name == "Primary":
        if ast.value is not None:
            if ast.sign == "-":
                return get_z3_operator_representation("neg", ast.value)
            elif ast.sign == "not":
                return get_z3_operator_representation("not", ast.value)
            else:
                if isinstance(ast.value, bool):
                    return z3.BoolSort().cast(ast.value)
                elif isinstance(ast.value, int):
                    return z3.IntSort().cast(ast.value)
                else:
                    return ast.value
        elif ast.ref is not None:
            if ast.sign == "-":
                return get_z3_operator_representation("neg", textx_to_z3py_model(ast.ref, variables))
            if ast.sign == "not":
                return get_z3_operator_representation("not", textx_to_z3py_model(ast.ref, variables))
            else:
                return textx_to_z3py_model(ast.ref, variables)
        else:
            if ast.sign == "-":
                return get_z3_operator_representation("neg", textx_to_z3py_model(ast.body, variables))
            if ast.sign == "not":
                return get_z3_operator_representation("not", textx_to_z3py_model(ast.body, variables))
            else:
                return textx_to_z3py_model(ast.body, variables)
    elif class_name == "ExpressionRef":
        if ast.index is None:
            return variables[ast.ref]
        else:
            return operator.itemgetter(textx_to_z3py_model(ast.index, variables))(variables[ast.ref])
    elif class_name == "VariableRef":
        if ast.index is None:
            return variables[ast.var.name]
        else:
            return operator.itemgetter(textx_to_z3py_model(ast.index, variables))(variables[ast.var.name])
    else:
        raise Exception("No implementation exists for the simple ast conversion of class [%s]" % class_name)


def add_z3py_annotations(model):
    """Add references to the z3py variables/expressions to the classes/state machines/expressions."""
    for c in model.classes:
        c.z3_variables = {v.name: get_z3py_variable(v) for v in c.variables}
        for sm in c.statemachines:
            sm.z3_variables = {**{v.name: get_z3py_variable(v) for v in sm.variables}, **c.z3_variables}

            # Annotate all expressions with z3 expressions.
            for t in sm.transitions:
                for s in t.statements:
                    if s.__class__.__name__ == "Expression":
                        s.z3py_expression = z3.simplify(textx_to_z3py_model(s, sm.z3_variables))
                        s.is_trivially_satisfiable = z3_check_trivially_satisfiable(s.z3py_expression)
                        s.is_trivially_unsatisfiable = z3_check_trivially_unsatisfiable(s.z3py_expression)

                    elif s.__class__.__name__ == "Composite":
                        s.guard.z3py_expression = z3.simplify(textx_to_z3py_model(s.guard, sm.z3_variables))
                        s.guard.is_trivially_satisfiable = z3_check_trivially_satisfiable(s.guard.z3py_expression)
                        s.guard.is_trivially_unsatisfiable = z3_check_trivially_unsatisfiable(s.guard.z3py_expression)


def print_decision_groups(tree, d=1):
    """Print the decision hierarchy with tab indents"""
    if tree.__class__.__name__ == "Transition":
        print("%s- %s" % ("\t" * d, tree))
    else:
        choice_type, members = tree
        print("%s- %s" % ("\t" * d, choice_type))
        for t in sorted(members, key=lambda v: v.__class__.__name__ != "Transition"):
            print_decision_groups(t, d + 1)


def print_determinism_report(state, sm, transitions, trivially_satisfiable, trivially_unsatisfiable):
    """Print a formatted report of the decision structure for the given state"""
    print("#" * 120)
    print("State Machine:", sm.name)
    print("State:", state)
    print()
    report_trivially_satisfiable = [
        t for t in trivially_satisfiable if t.guard_expression.smt is not True
    ]
    if len(report_trivially_satisfiable) > 0:
        print("WARNING: The following transition guards hold vacuously TRUE:")
        for t in report_trivially_satisfiable:
            print("\t- %s" % t)
        print()
    if len([t for t in trivially_unsatisfiable]) > 0:
        print("WARNING: The following transition guards are always FALSE:")
        for t in [t for t in trivially_unsatisfiable]:
            print("\t- %s" % t)
        print()
    print("Transitions:")
    if len(transitions) > 0:
        for t in transitions:
            print("\t- %s" % t)
        print()
        print("Decisions:")
        print_decision_groups(sm.groupings[state])
    else:
        print("\t- No transitions are defined.")
    print("#" * 120)
    print()


def format_decision_group_tree(tree):
    """Compress the decision group tree such that the decision type alternates per level"""
    if tree.__class__.__name__ == "Transition":
        return tree
    else:
        choice_type, members = tree
        compressed_members = []
        for m in members:
            m = format_decision_group_tree(m)

            if m.__class__.__name__ == "Transition":
                compressed_members.append(m)
            else:
                if m[0] != choice_type:
                    compressed_members.append(m)
                else:
                    compressed_members.extend(m[1])

        if len(compressed_members) == 1:
            return compressed_members[0]
        else:
            return choice_type, compressed_members


def dissect_overlapping_transition_chain(transitions, truth_matrices):
    """Dissect a list of transitions with a non-interrupted chain of overlap"""
    # Example input:                # Not allowed:
    # x -------    --------         # x -------
    # y     --------                # y            -------

    # Find the variables that are used in the transitions and group based on the chosen variables.
    variables_to_transitions = {}
    for t in transitions:
        used_variables = t.guard_expression.variables
        variables_to_transitions.setdefault(frozenset(used_variables), []).append(t)

    # Check if the groups can be split up more.
    groupings = [find_deterministic_groups(v, truth_matrices) for v in variables_to_transitions.values()]

    # The split needs to be resolved non-deterministically.
    return Decision.N_DET, groupings


def group_overlapping_transitions(transitions, and_truth_matrix):
    """Divide the transitions into groups, based on the equality measure"""
    # Transitions are in the same group if they have an equality relation with one another.
    groupings = []

    processed_transitions = set()
    queue = set()
    for t in transitions:
        if t not in processed_transitions:
            # Find all transitions that have an equality relation with this _t.
            queue.update([t2 for t2 in transitions if and_truth_matrix[t][t2]])

            current_group_transitions = []

            while len(queue) > 0:
                t2 = queue.pop()

                if t2 not in processed_transitions:
                    # Add the transition to the current group.
                    current_group_transitions += [t2]

                    # Find all transitions that are related to _t.
                    queue.update([t3 for t3 in transitions if and_truth_matrix[t2][t3]])

                    # We do not want to visit the queue head again.
                    processed_transitions.add(t2)

            # Can the found list of groupings be dissected further?
            sub_groupings = dissect_overlapping_transition_chain(current_group_transitions, and_truth_matrix)

            # Add the group to the list of groupings.
            groupings += [sub_groupings]

    # The result is always deterministic.
    return Decision.DET, groupings


def find_deterministic_groups(transitions, and_truth_matrix):
    """Find groups that are deterministic in regards to one another"""
    # Check whether we have a list of transitions to dissect.
    if len(transitions) == 1:
        return transitions[0]

    # Do any of the transitions always possibly overlap with the others transitions?
    # Keep in mind that the truth table has all transitions--only select those that we are examining.
    invariably_overlapping_transitions = [
        t for t in transitions if all(
            and_truth_matrix[t][t2] for t2 in transitions
        )
    ]

    # Find the transitions that are not invariably active.
    remaining_transitions = [t for t in transitions if t not in invariably_overlapping_transitions]

    # Recursively solve for the non invariably overlapping transitions.
    if len(remaining_transitions) > 0:
        remaining_groupings = [group_overlapping_transitions(remaining_transitions, and_truth_matrix)]
    else:
        remaining_groupings = []

    # The resulting sub-grouping is to be processed in parallel with the invariably active transitions.
    choices = invariably_overlapping_transitions + remaining_groupings
    return Decision.N_DET, choices


def calculate_and_truth_matrix(transitions):
    """Calculate the truth matrices for the transitions"""
    truth_matrix = {}
    for t in transitions:
        truth_matrix[t] = {}
        for t2 in transitions:
            truth_matrix[t][t2] = z3_check_and(t.guard_expression.z3py_expression, t2.guard_expression.z3py_expression)
    return truth_matrix


def annotate_decision_groupings(model):
    """Observe the transitions in the model and come up with decision structures"""
    for c in model.classes:
        for sm in c.statemachines:
            sm.groupings = {s: None for s in sm.adjacency_list.keys()}

            for state, transitions in sm.adjacency_list.items():
                if len(transitions) > 0:
                    if not settings.add_deterministic_structures:
                        # Force non-deterministic choices.
                        groupings = (Decision.N_DET, transitions) if len(transitions) > 1 else transitions[0]
                        sm.groupings[state] = format_decision_group_tree(groupings)
                    else:
                        # Are there transitions that are trivially (un)satisfiable?
                        trivially_satisfiable = [t for t in transitions if t.is_trivially_satisfiable]
                        trivially_unsatisfiable = [t for t in transitions if t.is_trivially_unsatisfiable]

                        # All transitions may be unsatisfiable and as such, the choices array can be empty.
                        if len(trivially_unsatisfiable) == len(transitions):
                            continue

                        # Find the transitions that remain.
                        solved_transitions = trivially_satisfiable + trivially_unsatisfiable
                        remaining_transitions = [t for t in transitions if t not in solved_transitions]

                        # Create a truth matrix for the and operation.
                        and_truth_matrix = calculate_and_truth_matrix(remaining_transitions)
                        choices = list(trivially_satisfiable)
                        if len(remaining_transitions) > 0:
                            choices += [find_deterministic_groups(remaining_transitions, and_truth_matrix)]

                        # If no transitions are trivially satisfiable, we do not need a N_DET wrapper.
                        groupings = (Decision.N_DET, choices) if len(choices) > 1 else choices[0]
                        sm.groupings[state] = format_decision_group_tree(groupings)

                print_determinism_report(state, sm, transitions, [], [])

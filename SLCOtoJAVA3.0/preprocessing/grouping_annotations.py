import operator
import z3

import settings
from util.z3py import z3_check_trivially_satisfiable, z3_check_trivially_unsatisfiable, z3_check_and, \
    get_z3py_variable, textx_to_z3py_model
from enum import Enum


class Decision(Enum):
    """A simple enum that denotes whether a decision is made deterministically or non-deterministically"""
    DET = 0
    N_DET = 1

    def __repr__(self):
        return self.__str__()


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


def split_on_used_variables(transitions, truth_matrices, stop_recursion=False):
    """Dissect a list of transitions based on the variables used"""
    if stop_recursion:
        return Decision.N_DET, transitions

    # Find the variables that are used in the transitions and group based on the chosen variables.
    variables_to_transitions = {}
    for t in transitions:
        used_variables = t.guard_expression.variables
        variables_to_transitions.setdefault(frozenset(used_variables), []).append(t)

    # Check if the groups can be split up more.
    groupings = [find_deterministic_groups(v, truth_matrices, True) for v in variables_to_transitions.values()]

    # The split needs to be resolved non-deterministically.
    return Decision.N_DET, groupings


def group_overlapping_transitions(transitions, and_truth_matrix, stop_recursion=False):
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
            sub_groupings = split_on_used_variables(current_group_transitions, and_truth_matrix, stop_recursion)

            # Add the group to the list of groupings.
            groupings += [sub_groupings]

    # The result is always deterministic.
    return Decision.DET, groupings


def find_deterministic_groups(transitions, and_truth_matrix, stop_recursion=False):
    """Find groups that are deterministic in regards to one another"""
    # Check whether we have a list of transitions to dissect.
    if len(transitions) == 1:
        return transitions[0]

    # Do any of the transitions always possibly overlap with the others transitions?
    # Keep in mind that the truth table has all transitions--only select those that we are examining.
    invariably_overlapping_transitions = [
        t for t in transitions if all(and_truth_matrix[t][t2] for t2 in transitions)
    ]

    # Find the transitions that are not invariably active.
    remaining_transitions = [t for t in transitions if t not in invariably_overlapping_transitions]

    # Recursively solve for the non invariably overlapping transitions.
    if len(remaining_transitions) > 0:
        remaining_groupings = [group_overlapping_transitions(remaining_transitions, and_truth_matrix, stop_recursion)]
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
                        trivially_unsatisfiable = [t for t in transitions if t.is_trivially_unsatisfiable]

                        # All transitions may be unsatisfiable and as such, the choices array can be empty.
                        if len(trivially_unsatisfiable) == len(transitions):
                            continue

                        # Find the transitions that remain.
                        solved_transitions = trivially_unsatisfiable # + trivially_satisfiable
                        remaining_transitions = [t for t in transitions if t not in solved_transitions]

                        # Create a truth matrix for the and operation.
                        and_truth_matrix = calculate_and_truth_matrix(remaining_transitions)
                        groupings = find_deterministic_groups(remaining_transitions, and_truth_matrix)
                        sm.groupings[state] = format_decision_group_tree(groupings)

                print_determinism_report(state, sm, transitions, [], [])

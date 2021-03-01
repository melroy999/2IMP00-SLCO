import z3

import settings
from preprocessing.grouping_annotations import format_decision_group_tree, print_determinism_report, Decision

# Keep a global instance of the z3 solver and cache solutions when possible.
s = z3.Optimize()


def z3_create_and_truth_table(transitions, alias_variables):
    """Create a truth table for the AND operation between the given list of transitions"""
    # Assign all transitions a unique id.
    for i, t in enumerate(transitions):
        t.i = i

    # Create the truth table.
    for t_2 in transitions:
        for t_1 in transitions:
            alias_variables["and%s_%s" % (t_1.i, t_2.i)] = z3.Bool("and%s_%s" % (t_1.i, t_2.i))

    for t_1 in transitions:
        for t_2 in transitions:
            if t_2.i > t_1.i:
                break

            # Add a new AND relation to the solver.
            e_1 = t_1.guard_expression.z3py_expression
            e_2 = t_2.guard_expression.z3py_expression

            # Existential quantifiers are not supported, so do the check separately.
            s.push()
            s.add(z3.And(e_1, e_2))
            result = s.check().r == z3.Z3_L_TRUE
            s.pop()

            # Add the constant to the solver.
            s.add(alias_variables["and%s_%s" % (t_1.i, t_2.i)] == result)
            if t_2.i < t_1.i:
                s.add(alias_variables["and%s_%s" % (t_2.i, t_1.i)] == alias_variables["and%s_%s" % (t_1.i, t_2.i)])


def merge_equal_solution_spaces(transitions):
    """Merge transitions that have the same solution space for the guard expression"""
    unique_solution_spaces = {}
    for t_1 in transitions:
        used_break = False
        for t_2 in unique_solution_spaces.keys():
            s.push()
            e_1 = t_1.guard_expression.z3py_expression
            e_2 = t_2.guard_expression.z3py_expression
            s.add(z3.Not(e_1 == e_2))
            result = s.check()
            s.pop()

            if result.r == z3.Z3_L_FALSE:
                # A duplicate has been found. Add to the duplicate.
                unique_solution_spaces[t_2].append(t_1)
                used_break = True
                break

        if not used_break:
            unique_solution_spaces[t_1] = []
    return unique_solution_spaces


def unpack_equal_solution_spaces(decision_node, unique_solution_spaces):
    """Unpack the unique solution spaces and add additional non-deterministic groups where necessary"""
    if isinstance(decision_node, tuple):
        # Unpack the node and alter the appropriate values.
        decision_type, groups = decision_node
        groups = [unpack_equal_solution_spaces(option, unique_solution_spaces) for option in groups]
        return decision_type, groups
    else:
        # A transition node has been found.
        if decision_node in unique_solution_spaces:
            # Replace the node with a non-deterministic decision.
            return Decision.N_DET, [decision_node] + unique_solution_spaces[decision_node]
        else:
            return decision_node


def extract_largest_deterministic_group(transitions, alias_variables):
    """Extract the largest combination of transitions that do not have an overlapping guard expression solution space"""
    # Single transitions cannot be extracted.
    if len(transitions) == 1:
        return list(transitions)

    # Save the current state of the solver.
    s.push()

    # First, create temporary variables that denote whether the transition is part of the group or not.
    for t_1 in transitions:
        v = alias_variables["g%s" % t_1.i] = z3.Int("g%s" % t_1.i)
        s.add(z3.And(v >= 0, v <= 1))

    # Ensure that a transition can only be assigned to the group if it does not overlap with the others.
    for t_1 in transitions:
        v = alias_variables["g%s" % t_1.i]
        s.add(z3.Implies(v == 1, z3.Not(z3.Or([
            z3.And(alias_variables["g%s" % t_2.i] == 1, alias_variables["and%s_%s" % (t_1.i, t_2.i)])
            for t_2 in transitions if t_1 != t_2
        ]))))

    # Maximize the sum such that we get the largest group possible.
    s.maximize(sum(alias_variables["g%s" % t.i] for t in transitions))

    # Get the model solution and extract the selected transitions.
    result, model = s.check(), s.model()
    if result.r == z3.Z3_L_UNDEF:
        print(result, model)
        raise Exception("Unknown result")
    if result.r == z3.Z3_L_FALSE:
        print(result, model)
        raise Exception("Unsatisfiable result")

    grouping = []
    for t in transitions:
        if model.evaluate(alias_variables["g%s" % t.i], model_completion=True) == 1:
            grouping.append(t)

    # Restore the state of the solver.
    s.pop()

    return grouping


def create_decision_groupings(transitions):
    """Convert the given list of transitions to a decision structure"""
    # Create a dictionary that will hold intermediate variables that are used to attain the solution.
    alias_variables = {}

    # Merge transitions with duplicate solution spaces.
    unique_solution_spaces = merge_equal_solution_spaces(transitions)
    target_transitions = unique_solution_spaces.keys()

    # Save the current state of the solver.
    s.push()

    # Create a truth table for the given transitions.
    z3_create_and_truth_table(target_transitions, alias_variables)

    # Keep extracting deterministic groups until no more unprocessed transitions remain.
    groupings = []
    remaining_transitions = set(target_transitions)
    while len(remaining_transitions) > 0:
        # Extract the largest group we can find.
        grouping = extract_largest_deterministic_group(remaining_transitions, alias_variables)

        # All transitions in the given grouping need to be removed from the list of remaining transitions.
        remaining_transitions.difference_update(grouping)

        # Add the grouping to the list of groupings in the shape of a deterministic block.
        groupings.append((Decision.DET, grouping) if len(grouping) > 1 else grouping[0])

    # Restore the state of the solver.
    s.pop()

    # Create the top level decision structure.
    top_decision_node = Decision.N_DET, groupings

    # Unpack transitions with duplicate solution spaces and alter the groupings accordingly.
    return unpack_equal_solution_spaces(top_decision_node, unique_solution_spaces)


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

                        # Find the transitions that remain and create groupings.
                        remaining_transitions = [t for t in transitions if t not in trivially_unsatisfiable]
                        groupings = create_decision_groupings(remaining_transitions)
                        sm.groupings[state] = format_decision_group_tree(groupings)

                # Print a debug report.
                if settings.add_debug_prints:
                    print_determinism_report(state, sm, transitions, [], [])

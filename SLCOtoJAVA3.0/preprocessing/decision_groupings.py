from enum import Enum


class Decision(Enum):
    """A simple enum that denotes whether a decision is made deterministically or non-deterministically"""
    DET = 0
    N_DET = 1

    def __repr__(self):
        return self.__str__()


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
    """Compress the decision group tree such that the decision type alternates per level.
    Moreover, all transitions with guards should be part of a deterministic group"""
    if tree.__class__.__name__ == "Transition":
        # A transition should always be wrapped by a deterministic choice, unless trivially satisfiable.
        if tree.is_trivially_satisfiable:
            return tree
        else:
            return Decision.DET, [tree]
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


def annotate_decision_groupings(model):
    """Observe the transitions in the model and come up with decision structures"""
    for c in model.classes:
        for sm in c.statemachines:
            sm.groupings = {s: None for s in sm.adjacency_list.keys()}

            for state, transitions in sm.adjacency_list.items():
                if len(transitions) > 0:
                    # Are there transitions that are trivially (un)satisfiable?
                    trivially_satisfiable = [t for t in transitions if t.is_trivially_satisfiable]
                    trivially_unsatisfiable = [t for t in transitions if t.is_trivially_unsatisfiable]

                    # All transitions may be unsatisfiable and as such, the choices array can be empty.
                    if len(trivially_unsatisfiable) == len(transitions):
                        continue

                    # Find the transitions that remain.
                    solved_transitions = trivially_satisfiable + trivially_unsatisfiable
                    remaining_transitions = [t for t in transitions if t not in solved_transitions]

                    # TODO For now, top-level choices are always non-deterministic.
                    choices = list(trivially_satisfiable + remaining_transitions)

                    # If no transitions are trivially satisfiable, we do not need a N_DET wrapper.
                    groupings = (Decision.N_DET, choices) if len(choices) > 1 else choices[0]
                    sm.groupings[state] = format_decision_group_tree(groupings)

                print_determinism_report(state, sm, transitions, [], [])

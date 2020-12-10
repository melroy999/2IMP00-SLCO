import z3

# Keep a global instance of the z3 solver and cache solutions when possible.
s = z3.Solver()


def z3_check_trivially_satisfiable(expression):
    """Check whether the given expression always holds true"""
    s.push()
    s.add(z3.Not(expression))
    result = s.check()
    s.pop()

    # The expression always holds true if the negation is satisfiable.
    return result.r == z3.Z3_L_FALSE


def z3_check_trivially_unsatisfiable(expression):
    """Check whether the given expression has no solutions"""
    s.push()
    s.add(expression)
    result = s.check()
    s.pop()

    # The expression has no solutions if the model is unsatisfiable.
    return result.r == z3.Z3_L_FALSE


def z3_do_magic(transitions, variables):
    s.push()

    # Create a truth matrix for AND.
    alias_variables = {}
    for i_2 in range(len(transitions)):
        for i_1 in range(len(transitions)):
            alias_variables["and%s_%s" % (i_1, i_2)] = z3.Bool("and%s_%s" % (i_1, i_2))

    variables = [v for v in variables.values()]
    for i_1 in range(len(transitions)):
        for i_2 in range(len(transitions)):
            if i_2 > i_1:
                break

            # Add a new AND relation to the solver.
            e_1 = transitions[i_1].guard_expression.z3py_expression
            e_2 = transitions[i_2].guard_expression.z3py_expression
            and_1_2 = z3.simplify(z3.And(e_1, e_2))
            s.add(alias_variables["and%s_%s" % (i_1, i_2)] == z3.Exists(variables, and_1_2))
            if i_2 < i_1:
                s.add(alias_variables["and%s_%s" % (i_2, i_1)] == alias_variables["and%s_%s" % (i_1, i_2)])

    result, model = s.check(), s.model()
    for ev in ["and"]:
        print(ev.upper())
        for i_1 in range(len(transitions)):
            for i_2 in range(len(transitions)):
                evaluation = model.evaluate(alias_variables["%s%s_%s" % (ev, i_1, i_2)], model_completion=True)
                print("%s %s %s: %s" % (
                    transitions[i_1].guard_expression,
                    ev.upper(),
                    transitions[i_2].guard_expression,
                    evaluation
                ))
            print()
        print()

    # Assign every transition to a group and assure the groups are in a reasonable range.
    for i in range(len(transitions)):
        v = alias_variables["g%s" % i] = z3.Int("g%s" % i)
        s.add([z3.And(v >= 0, v < len(transitions)) for i in range(len(transitions))])

    # Transitions need to be in the same group if they overlap in the solution space.
    for i_1 in range(len(transitions)):
        for i_2 in range(len(transitions)):
            if i_2 > i_1:
                break

            g_1 = alias_variables["g%s" % i_1]
            g_2 = alias_variables["g%s" % i_2]
            s.add(z3.Implies(alias_variables["and%s_%s" % (i_2, i_1)], g_1 == g_2))

    # Ensure that transitions that are not in the same group get assigned different groups ids.
    for i_1 in range(len(transitions)):
        for i_2 in range(len(transitions)):
            if i_2 >= i_1:
                break

            if i_2 < i_1:
                g_1 = alias_variables["g%s" % i_1]
                g_2 = alias_variables["g%s" % i_2]
                and_1_2 = alias_variables["and%s_%s" % (i_1, i_2)]

                others = []
                for i in range(len(transitions)):
                    if i not in [i_1, i_2]:
                        g_i = alias_variables["g%s" % i]
                        and_1_i = alias_variables["and%s_%s" % (i_1, i)]
                        and_2_i = alias_variables["and%s_%s" % (i_2, i)]
                        others.append(z3.Or(z3.And(g_1 == g_i, and_1_i), z3.And(g_2 == g_i, and_2_i)))

                s.add(z3.Implies(z3.And(g_1 == g_2, z3.Not(and_1_2)), z3.Or(others)))

    result, model = s.check(), s.model()
    for i in range(len(transitions)):
        evaluation = model.evaluate(alias_variables["g%s" % i], model_completion=True)
        print("%s in group %s" % (transitions[i].guard_expression, evaluation))
    print()

    s.pop()

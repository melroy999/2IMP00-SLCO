import operator
import z3

# Keep a global instance of the z3 solver and cache solutions when possible.
solver = z3.Solver()

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


def z3_check_trivially_satisfiable(expression):
    """Check whether the given expression always holds true"""
    solver.push()
    solver.add(z3.Not(expression))
    result = solver.check()
    solver.pop()

    # The expression always holds true if the negation is satisfiable.
    return result.r == z3.Z3_L_FALSE


def z3_check_trivially_unsatisfiable(expression):
    """Check whether the given expression has no solutions"""
    solver.push()
    solver.add(expression)
    result = solver.check()
    solver.pop()

    # The expression has no solutions if the model is unsatisfiable.
    return result.r == z3.Z3_L_FALSE


def z3_check_and(e1, e2, for_all=False):
    """Check whether there is a solution to the conjunction of the two expressions"""
    solver.push()
    if for_all:
        solver.add(z3.Not(z3.And(e1, e2)))
    else:
        solver.add(z3.And(e1, e2))
    result = solver.check()
    solver.pop()

    if for_all:
        return result.r == z3.Z3_L_FALSE
    else:
        return result.r == z3.Z3_L_TRUE


def z3_check_implies(e1, e2, for_all=False):
    """Check whether there is a solution to the implication of the two expressions"""
    solver.push()
    if for_all:
        solver.add(z3.Not(z3.Implies(e1, e2)))
    else:
        solver.add(z3.Implies(e1, e2))
    result = solver.check()
    solver.pop()

    if for_all:
        return result.r == z3.Z3_L_FALSE
    else:
        return result.r == z3.Z3_L_TRUE


def z3_check_equality(e1, e2, for_all=False):
    """Check whether there is a solution to the equality of the two expressions"""
    solver.push()
    if for_all:
        solver.add(z3.Not(e1 == e2))
    else:
        solver.add(e1 == e2)
    result = solver.check()
    solver.pop()

    if for_all:
        return result.r == z3.Z3_L_FALSE
    else:
        return result.r == z3.Z3_L_TRUE


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

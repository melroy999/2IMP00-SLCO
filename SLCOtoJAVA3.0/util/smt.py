import z3


class TransitDict(dict):
    """A dictionary that returns the key upon query if the key is not present within the dictionary"""
    def __missing__(self, key):
        return key


# Convert the used symbols to their Z3 SMT2.0 counterpart.
smt_operator_mappings = TransitDict()
smt_operator_mappings["<>"] = "!="
smt_operator_mappings["!"] = "not"
smt_operator_mappings["&&"] = "and"
smt_operator_mappings["||"] = "or"
smt_operator_mappings["%"] = "mod"


def to_simple_ast(ast):
    """Convert the TextX expression AST to a simpler and more tidy format similar to the SMT2.0 standard"""
    class_name = ast.__class__.__name__
    if class_name in ["Expression", "ExprPrec1", "ExprPrec2", "ExprPrec3", "ExprPrec4"]:
        if ast.right is None:
            return to_simple_ast(ast.left)
        else:
            return smt_operator_mappings[ast.op], to_simple_ast(ast.left), to_simple_ast(ast.right)
    elif class_name == "Primary":
        if ast.value is not None:
            if ast.sign == "-":
                return -1 * ast.value
            elif ast.sign == "not":
                return not ast.value
            else:
                return ast.value
        elif ast.ref is not None:
            if ast.sign == "-":
                return "-", 0, to_simple_ast(ast.ref)
            if ast.sign == "not":
                return "not", to_simple_ast(ast.ref)
            return to_simple_ast(ast.ref)
        else:
            if ast.sign == "-":
                return "-", 0, to_simple_ast(ast.body)
            if ast.sign == "not":
                return "not", to_simple_ast(ast.body)
            else:
                return to_simple_ast(ast.body)
    elif class_name == "ExpressionRef":
        if ast.index is None:
            return "var", ast.ref
        else:
            return "var[]", ast.ref, to_simple_ast(ast.index)
    elif class_name == "VariableRef":
        if ast.index is None:
            return "var", ast.var.name
        else:
            return "var[]", ast.var.name, to_simple_ast(ast.index)
    else:
        raise Exception("No implementation exists for the simple ast conversion of class [%s]" % class_name)

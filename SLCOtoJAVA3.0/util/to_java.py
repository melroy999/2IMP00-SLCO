class TransitDict(dict):
    """A dictionary that returns the key upon query if the key is not present within the dictionary"""
    def __missing__(self, key):
        return key


# Conversion from SLCO to Java operators.
java_operator_mappings = TransitDict()
java_operator_mappings["<>"] = "!="
java_operator_mappings["="] = "=="
java_operator_mappings["and"] = "&&"
java_operator_mappings["or"] = "||"
java_operator_mappings["not"] = "!"


def get_instruction(m, rewrite_table=None):
    """Get the Java code associated with a given SLCO statement."""
    if rewrite_table is None:
        rewrite_table = {}
    model_class = m.__class__.__name__

    if model_class == "Assignment":
        index_str = "[" + get_instruction(m.left.index, rewrite_table) + "]" if m.left.index is not None else ""
        var_str = m.left.var.name + index_str
        exp_str = "%s" % get_instruction(m.right, rewrite_table)
        return "%s = %s" % (var_str, exp_str)
    elif model_class == "Composite":
        statement_strings = [get_instruction(m.guard, rewrite_table)] if not m.guard.is_trivially_satisfiable else []
        statement_strings += [get_instruction(s, rewrite_table) for s in m.assignments]
        return "[%s]" % "; ".join(statement_strings)
    elif model_class in ["Expression", "ExprPrec1", "ExprPrec2", "ExprPrec3", "ExprPrec4"]:
        if m.op == "":
            return get_instruction(m.left, rewrite_table)
        elif m.op == "**":
            left_str = get_instruction(m.left, rewrite_table)
            right_str = get_instruction(m.right, rewrite_table)
            return "(int) Math.pow(%s, %s)" % (left_str, right_str)
        elif m.op == "%":
            # The % operator in Java is the remainder operator, which is not the modulo operator.
            left_str = get_instruction(m.left, rewrite_table)
            right_str = get_instruction(m.right, rewrite_table)
            return "Math.floorMod(%s, %s)" % (left_str, right_str)
        else:
            left_str = get_instruction(m.left, rewrite_table)
            right_str = get_instruction(m.right, rewrite_table)
            return "%s %s %s" % (left_str, java_operator_mappings[m.op], right_str)
    elif model_class == "Primary":
        if m.value is not None:
            exp_str = str(m.value).lower()
        elif m.ref is not None:
            var_str = m.ref.ref
            if m.ref.index is not None:
                var_str += "[%s]" % get_instruction(m.ref.index, rewrite_table)
            exp_str = rewrite_table.get(var_str, var_str)
        else:
            exp_str = "(%s)" % get_instruction(m.body, rewrite_table)
        return ("!(%s)" if m.sign == "not" else m.sign + "%s") % exp_str
    elif model_class == "VariableRef":
        var_str = m.var.name
        if m.index is not None:
            var_str += "[%s]" % get_instruction(m.index, rewrite_table)
        return rewrite_table.get(var_str, var_str)
    else:
        return "// NYI [%s]" % model_class


def get_java_type(model, ignore_size=False):
    """Maps type names from SLCO to Java"""
    if model.base == "Boolean":
        return "boolean" if model.size < 1 or ignore_size else "boolean[]"
    elif model.base in ["Integer", "Byte"]:
        # Note: Bytes need to be handled as integers, since unsigned bytes do not exist in Java.
        return "int" if model.size < 1 or ignore_size else "int[]"


def get_initial_value(model):
    """Return the initial value of the given variable"""
    if model.defvalue is not None:
        value = model.defvalue
    elif len(model.defvalues) > 0:
        value = [v for v in model.defvalues]
    else:
        value = get_default_value(model)

    return "{%s}" % ", ".join(str(v).lower() for v in value) if isinstance(value, list) else str(value).lower()


def get_default_value(model):
    """Return a default value for the given variable"""
    if model.type.base in ["Integer", "Byte"]:
        return 0 if model.type.size < 1 else [0 for _ in range(0, model.type.size)]
    else:
        return True if model.type.size < 1 else [True for _ in range(0, model.type.size)]

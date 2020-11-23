# Import the necessary libraries.
import jinja2

import settings


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


def get_instruction(m):
    """Get the Java code associated with a given SLCO statement."""
    model_class = m.__class__.__name__

    if model_class == "Assignment":
        var_str = m.left.var.name + ("[" + get_instruction(m.left.index) + "]" if m.left.index is not None else "")
        exp_str = ("(byte) (%s)" if m.left.var.type.base == "Byte" else "%s") % get_instruction(m.right)
        return "%s = %s" % (var_str, exp_str)
    elif model_class == "Composite":
        statement_strings = [get_instruction(m.guard)] if not m.guard.is_trivially_satisfiable else []
        statement_strings += [get_instruction(s) for s in m.assignments]
        return "[%s]" % "; ".join(statement_strings)
    elif model_class in ["Expression", "ExprPrec1", "ExprPrec2", "ExprPrec3", "ExprPrec4"]:
        if m.op == "":
            return get_instruction(m.left)
        elif m.op == "**":
            return "(int) Math.pow(%s, %s)" % (get_instruction(m.left), get_instruction(m.right))
        elif m.op == "%":
            # The % operator in Java is the remainder operator, which is not the modulo operator.
            return "Math.floorMod(%s, %s)" % (get_instruction(m.left), get_instruction(m.right))
        else:
            return "%s %s %s" % (get_instruction(m.left), java_operator_mappings[m.op], get_instruction(m.right))
    elif model_class == "Primary":
        if m.value is not None:
            exp_str = str(m.value).lower()
        elif m.ref is not None:
            exp_str = m.ref.ref + ("[%s]" % get_instruction(m.ref.index) if m.ref.index is not None else "")
        else:
            exp_str = "(%s)" % get_instruction(m.body)
        return ("!(%s)" if m.sign == "not" else m.sign + "%s") % exp_str
    elif model_class == "VariableRef":
        return m.var.name + ("[%s]" % get_instruction(m.index) if m.index is not None else "")
    else:
        return "// NYI [%s]" % model_class


def comma_separated_list(model):
    """Construct a comma separated list of the given iterable"""
    return ", ".join(model)


def get_java_type(model, ignore_size):
    """Maps type names from SLCO to Java"""
    if model.base == "Boolean":
        return "boolean" if model.size < 1 or ignore_size else "boolean[]"
    elif model.base == "Integer":
        return "int" if model.size < 1 or ignore_size else "int[]"
    elif model.base == "Byte":
        return "byte" if model.size < 1 or ignore_size else "byte[]"


def get_default_value(model):
    """Return a default value for the given variable"""
    if model.type.base in ["Integer", "Byte"]:
        return 0 if model.type.size < 1 else [0 for _ in range(0, model.type.size)]
    else:
        return True if model.type.size < 1 else [True for _ in range(0, model.type.size)]


def get_initial_value(model):
    """Return the initial value of the given variable"""
    if model.defvalue is not None:
        value = model.defvalue
    elif len(model.defvalues) > 0:
        value = [v for v in model.defvalues]
    else:
        value = get_default_value(model)

    return "{%s}" % ", ".join(str(v).lower() for v in value) if isinstance(value, list) else str(value).lower()


def get_variable_list(model):
    """Construct a comma separated list of variables, sorted on by name and prefixed with their type"""
    variables = ["%s %s" % (get_java_type(_v.type, False), _v.name) for _v in sorted(model, key=lambda v: v.name)]
    return comma_separated_list(variables)


def get_variable_instantiation_list(model, variables):
    """Construct a comma separated list of variable initializations sorted on by name"""
    # The initialization of class variables are processed per initialization.
    instantiated_variables = {
        _v.left.name: _v.rights if _v.right is None else _v.right for _v in model
    }

    variable_instantiations = []
    for v in sorted(variables, key=lambda o: o.name):
        # Is a value assigned to the variable? If so, use it, otherwise, fall back to the default.
        value = instantiated_variables[v.name] if v.name in instantiated_variables else get_default_value(v)

        # Convert the variable to the Java representation.
        value = "{%s}" % ", ".join(str(v).lower() for v in value) if isinstance(value, list) else str(value).lower()

        if v.type.size > 1:
            variable_instantiations.append("new %s %s" % (get_java_type(v.type, False), value))
        elif v.type.base == "Byte":
            variable_instantiations.append("(byte) %s" % value)
        else:
            variable_instantiations.append("%s" % value)
    return comma_separated_list(variable_instantiations)


def get_guard_statement(model):
    """Construct an or-code-clause encapsulating all guard expressions for the target decision block"""
    if model.__class__.__name__ == "TransitionBlock":
        return get_instruction(model.guard_expression)
    else:
        # Construct a disjunction of statements. Brackets are not needed because of the precedence order.
        # TODO simplify using SMT.
        #   - Remove formulas that are equivalent to an already encountered formula.
        #   - Use implication to check whether one formula is contained in another?
        return " || ".join([get_instruction(e) for e in model.encapsulating_guard_expression])


def render_model(model):
    """Convert the SLCO model to Java code"""
    return java_model_template.render(
        model=model,
        add_counter=settings.add_counter,
    )


def render_class(c):
    """Convert the SLCO class to Java code"""
    return java_class_template.render(
        model=c
    )


def render_state_machine(sm, c):
    """Convert the SLCO state machine to Java code"""
    return java_state_machine_template.render(
        model=sm,
        add_counter=settings.add_counter,
        _c=c
    )


# Initialize the template engine.
env = jinja2.Environment(
    loader=jinja2.FileSystemLoader('jinja2_templates'),
    trim_blocks=True,
    lstrip_blocks=True,
    extensions=['jinja2.ext.loopcontrols', 'jinja2.ext.do']
)

# Register the filters
env.filters['render_class'] = render_class
env.filters['render_state_machine'] = render_state_machine

env.filters['comma_separated_list'] = comma_separated_list
env.filters['get_java_type'] = get_java_type
env.filters['get_initial_value'] = get_initial_value
env.filters['get_instruction'] = get_instruction
env.filters['get_guard_statement'] = get_guard_statement
env.filters['get_variable_list'] = get_variable_list
env.filters['get_variable_instantiation_list'] = get_variable_instantiation_list

# env.filters['get_decision_structure'] = get_decision_structure
# env.filters['to_comma_separated_lock_name_list'] = to_comma_separated_lock_name_list
# env.filters['to_comma_separated_lock_id_list'] = to_comma_separated_lock_id_list

# Load the Java templates.
java_model_template = env.get_template('java_model.jinja2template')
java_class_template = env.get_template('java_class.jinja2template')
java_state_machine_template = env.get_template('java_state_machine.jinja2template')
java_transition_template = env.get_template('java_transition.jinja2template')

java_assignment_template = env.get_template('statements/java_assignment.jinja2template')
java_expression_template = env.get_template('statements/java_expression.jinja2template')
java_composite_template = env.get_template('statements/java_composite.jinja2template')

java_if_then_else_template = env.get_template('decision_structures/java_if_then_else.jinja2template')
java_case_distinction_template = env.get_template('decision_structures/java_case_distinction.jinja2template')
java_pick_randomly_template = env.get_template('decision_structures/java_pick_randomly.jinja2template')

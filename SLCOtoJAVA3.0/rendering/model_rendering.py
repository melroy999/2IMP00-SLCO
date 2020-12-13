# Import the necessary libraries.
import jinja2
from z3 import z3

import settings
from rendering.view_models import get_view_model
from util.z3py import z3_check_trivially_satisfiable, z3_check_implies, z3_check_equality


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
        exp_str = ("(byte) (%s)" if m.left.var.type.base == "Byte" else "%s") % get_instruction(m.right, rewrite_table)
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


def comma_separated_list(model):
    """Construct a comma separated list of the given iterable"""
    return ", ".join(model)


def get_lock_id_list(model, c):
    """Construct a list of all the targeted lock ids, sorted on variable/primary lock id name"""
    lock_ids = []
    for v, i in sorted(model, key=lambda _o: (c.name_to_variable[_o[0]].lock_id, str(_o[1]).strip("()"))):
        base = c.name_to_variable[v].lock_id
        index = 0 if i is None else i
        try:
            index = int(index)
            lock = str(base + index)
        except (ValueError, TypeError):
            if base == 0:
                lock = index
            else:
                lock = "%s + %s" % (base, index)
        lock += "; // Acquire " + v + ("" if i is None else "[%s]" % i)
        lock_ids.append(lock)
    return lock_ids


def get_java_type(model, ignore_size):
    """Maps type names from SLCO to Java"""
    if model.base == "Boolean":
        return "boolean" if model.size < 1 or ignore_size else "boolean[]"
    elif model.base == "Integer":
        return "int" if model.size < 1 or ignore_size else "int[]"
    elif model.base == "Byte":
        return "byte" if model.size < 1 or ignore_size else "byte[]"


def get_sync_type(model):
    """Returns final or volatile when applicable"""
    return "volatile" if model.size < 1 else "final"


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


def get_variable_instantiation_list(model, variables, use_newline):
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

    if use_newline:
        return ",\n".join(variable_instantiations)
    else:
        return comma_separated_list(variable_instantiations)


def get_guard_statement(model):
    """Construct an or-code-clause encapsulating all guard expressions for the target decision block"""
    if model.__class__.__name__ == "TransitionBlock":
        return get_instruction(model.guard_expression)
    else:
        # Remove statements that have the same solution space.
        duplicate_expressions = set([])
        for e_1 in model.guard_expressions:
            for e_2 in model.guard_expressions:
                if e_1 == e_2:
                    break
                if z3_check_equality(e_1.z3py_expression, e_2.z3py_expression, True):
                    duplicate_expressions.add(e_1)
        guard_expressions = [e for e in model.guard_expressions if e not in duplicate_expressions]

        # Check if expressions are superfluous, i.e., contained within another statement.
        implies_truth_matrix = {}
        for e_1 in guard_expressions:
            implies_truth_matrix[e_1] = {}
            for e_2 in guard_expressions:
                if e_1 == e_2:
                    implies_truth_matrix[e_1][e_2] = False
                else:
                    implies_truth_matrix[e_1][e_2] = z3_check_implies(e_1.z3py_expression, e_2.z3py_expression, True)

        # If any of the values is true, remove the guard expression from the result, since it is included in another.
        target_expressions = []
        for e_1 in guard_expressions:
            if e_1 not in duplicate_expressions and not any(implies_truth_matrix[e_1].values()):
                target_expressions.append(e_1)

        # Construct a disjunction of statements. Brackets are not needed because of the precedence order.
        return " || ".join([get_instruction(e) for e in target_expressions])


def construct_decision_code(model, sm, include_guard=True, include_comment=True):
    """Convert the decision structure to Java code"""
    model_class = model.__class__.__name__
    if model_class == "TransitionBlock":
        statements = [construct_decision_code(s, sm) for s in model.statements]
        return java_transition_template.render(
            statements=statements,
            target=model.target,
            state_machine_name=sm.name,
            always_fails=model.always_fails,
            comment=model.comment if include_comment else None,
            _c=sm.parent_class,
            transition_identifier=model.comment
        )
    elif model_class == "Composite":
        guard = model.guard if not model.guard.is_trivially_satisfiable and include_guard else None
        return java_composite_template.render(
            guard=guard,
            assignments=model.assignments,
            lock_request_phases=model.lock_request_phases,
            number_of_locks=len(model.lock_requests),
            lock_ranges=model.lock_ranges,
            _c=sm.parent_class
        )
    elif model_class == "Assignment":
        return java_assignment_template.render(
            assignment=model,
            lock_request_phases=model.lock_request_phases,
            number_of_locks=len(model.lock_requests),
            lock_ranges=model.lock_ranges,
            _c=sm.parent_class
        )
    elif model_class == "Expression":
        return java_expression_template.render(
            expression=model,
            lock_request_phases=model.lock_request_phases,
            number_of_locks=len(model.lock_requests),
            lock_ranges=model.lock_ranges,
            _c=sm.parent_class
        )
    elif model_class == "ActionRef":
        return "// Execute action [%s]\n" % model.act.name
    elif model_class == "NonDeterministicBlock":
        # Several of the choices may have the same conversion string. Filter these out and merge.
        choices = [construct_decision_code(choice, sm) for choice in model.choice_blocks]
        choices.sort(key=lambda v: v[0])

        # If only one choice remains, there is no reason to include an entire block.
        if len(choices) == 1:
            return choices[0]

        return java_pick_randomly_template.render(
            choices=choices,
            _c=sm.parent_class
        )
    elif model_class == "DeterministicIfThenElseBlock":
        # Order the choices such that the generated code is always the same.
        choices = [
            (construct_decision_code(choice, sm), get_guard_statement(choice)) for choice in model.choice_blocks
        ]
        choices.sort(key=lambda v: v[0])

        # Does the combination of all the guards always evaluate to true?
        else_choice = None
        encapsulating_guard_expression = z3.Or([e.z3py_expression for e in model.guard_expressions])
        if len(model.guard_expressions) > 0 and z3_check_trivially_satisfiable(encapsulating_guard_expression):
            else_choice = choices[-1]
            choices = choices[:-1]

        return java_if_then_else_template.render(
            choices=choices,
            else_choice=else_choice,
            _c=sm.parent_class
        )
    elif model_class == "DeterministicCaseDistinctionBlock":
        # Several of the choices may have the same conversion string. Filter these out and merge.
        choices = [
            (
                target,
                construct_decision_code(choice, sm, include_comment=False),
                choice.comment if choice.__class__.__name__ == "TransitionBlock" else None
            ) for (target, choice) in model.choice_blocks
        ]
        choices.sort(key=lambda v: v[1])

        subject_expression = get_instruction(model.subject_expression)
        default_decision_tree = construct_decision_code(model.default_decision_tree, sm)
        return java_case_distinction_template.render(
            subject_expression=subject_expression,
            default_decision_tree=default_decision_tree,
            choices=choices,
            _c=sm.parent_class
        )


def get_decision_structure(groupings, sm):
    view_model = get_view_model(groupings, sm.parent_class)
    return construct_decision_code(view_model, sm)


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
        _c=c,
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
env.filters['get_sync_type'] = get_sync_type
env.filters['get_initial_value'] = get_initial_value
env.filters['get_instruction'] = get_instruction
env.filters['get_guard_statement'] = get_guard_statement
env.filters['get_variable_list'] = get_variable_list
env.filters['get_variable_instantiation_list'] = get_variable_instantiation_list

env.filters['get_decision_structure'] = get_decision_structure
env.filters['get_lock_id_list'] = get_lock_id_list

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

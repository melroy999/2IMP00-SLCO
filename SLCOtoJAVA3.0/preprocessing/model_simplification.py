

def get_used_variables(model, used_variables):
    """Gather the variables that are used by the model"""
    class_name = model.__class__.__name__

    if class_name == "StateMachine":
        for t in model.transitions:
            get_used_variables(t, used_variables)
    elif class_name == "Transition":
        for t in model.statements:
            get_used_variables(t, used_variables)
    elif class_name == "Composite":
        get_used_variables(model.guard, used_variables)
        for t in model.assignments:
            get_used_variables(t, used_variables)
    elif class_name in ["Assignment", "Expression", "ExprPrec1", "ExprPrec2", "ExprPrec3", "ExprPrec4"]:
        get_used_variables(model.left, used_variables)
        if model.right is not None:
            get_used_variables(model.right, used_variables)
    elif class_name == "ExpressionRef":
        used_variables.update({model.ref})
        if model.index is not None:
            # The index might hide a variable within it.
            get_used_variables(model.index, used_variables)
    elif class_name == "VariableRef":
        used_variables.update({model.var.name})
        if model.index is not None:
            # The index might hide a variable within it.
            get_used_variables(model.index, used_variables)
    elif class_name == "Primary" and model.ref is not None:
        get_used_variables(model.ref, used_variables)


def remove_unused_variables(model):
    """Remove variables that aren't used in the model"""
    for c in model.classes:
        # Keep a list of used variables per class.
        variables_used_in_class = set([])

        for sm in c.statemachines:
            used_variables = set([])
            get_used_variables(sm, used_variables)
            variables_used_in_class = variables_used_in_class.union(used_variables)

            # Check if there are unused local variables. If there are, remove them from the model.
            sm.variables = [v for v in sm.variables if v.name in used_variables]

        # Check if there are unused global variables. If there are, remove them from the model.
        c.variables = [v for v in c.variables if v.name in variables_used_in_class]

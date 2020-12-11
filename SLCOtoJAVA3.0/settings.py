add_counter = False
add_performance_counter = False
print_decision_report = False
add_deterministic_structures = True


def init(add_counter_var, add_deterministic_structures_var):
    """Initialize the global variables, defining the settings of the program"""
    global add_counter, add_performance_counter, print_decision_report, add_deterministic_structures
    add_counter = add_counter_var
    add_deterministic_structures = add_deterministic_structures_var

add_counter = False
add_performance_counter = False
print_decision_report = False
add_deterministic_structures = True
use_smt_solution = False


def init(add_counter_var, add_deterministic_structures_var, use_smt_solution_var):
    """Initialize the global variables, defining the settings of the program"""
    global add_counter, add_performance_counter, print_decision_report, add_deterministic_structures, use_smt_solution
    add_counter = add_counter_var
    add_deterministic_structures = add_deterministic_structures_var
    use_smt_solution = use_smt_solution_var

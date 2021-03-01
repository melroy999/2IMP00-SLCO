# Add a limit on the number of iterations.
import os

add_counter = False
max_nr_of_iterations = 0

# Add a limit on the running time.
add_timer = False
max_running_time = 0

# Add deterministic structures to the code.
add_deterministic_structures = True

# The target model and folder.
model_name = ""
model_folder = ""

# Add the performance counters used for performance testing.
add_performance_counter = False

# Add debug prints to the generator such as the assigned lock identities and decision structures.
add_debug_prints = False


def init(parameters):
    """Initialize the global variables, defining the settings of the program"""
    global add_counter, max_nr_of_iterations, add_timer, max_running_time, add_deterministic_structures, \
        add_deterministic_structures, model_folder, model_name, add_performance_counter, add_debug_prints

    # Print the input parameters for debug purposes.
    if parameters.v:
        print(parameters)

    # Add a counter to the code counting down from the specified number.
    if parameters.c != 0:
        add_counter = True
        max_nr_of_iterations = parameters.c

    # Add a limit on the running time of the program in seconds.
    if parameters.t != 0:
        add_timer = True
        max_running_time = parameters.t

    # Add deterministic structures to the code.
    add_deterministic_structures = not parameters.nds

    # Add the performance counters used for performance testing.
    add_performance_counter = parameters.pc

    # Add debug prints to the generator such as the assigned lock identities and decision structures.
    add_debug_prints = parameters.v

    # Add the name of the model and the location.
    model_folder, model_name = os.path.split(parameters.model)

# Import the necessary libraries.
import os

import settings
from libraries.slcolib import *
from preprocessing.model_annotations import annotate_model
from preprocessing.model_simplification import remove_unused_variables
from rendering.model_rendering import render_model


def preprocess(model):
    """"Gather additional data about the model"""
    # Cleanup the model and remove superfluous objects.
    remove_unused_variables(model)

    # Extend and annotate the model to one fitting our purpose.
    annotate_model(model)

    # Find which transitions can be executed with determinism and add the required information to the model.
    # TODO add_determinism_annotations(model)


def render(model, model_folder):
    """The translation function"""
    out_file = open(os.path.join(model_folder, model.name + ".java"), 'w')

    # Write the program to the desired output file.
    out_file.write(
        render_model(model)
    )
    out_file.close()


def main(_args):
    """The main function"""
    model_folder, model_name = None, None

    # Set defaults for the modifier parameters.
    add_counter = False

    # Parse the parameters.
    if any([arg in ["-h", "-help"] for arg in _args]):
        print("Usage: pypy/python3 slco2java")
        print("")
        print("Transform an SLCO 2.0 model to a Java program.")
        print("-c                 produce a transition counter in the code, to make program executions finite")
        sys.exit(0)
    else:
        _i = 0
        while _i < len(_args):
            if _args[_i] == '-c':
                add_counter = True
            else:
                model_folder, model_name = os.path.split(_args[_i])
            _i += 1

        if model_folder is None:
            print("Missing argument: SLCO model")
            sys.exit(1)

    # Store the settings for this run.
    settings.init(add_counter)

    # Read the model and preprocess it.
    model = read_SLCO_model(os.path.join(model_folder, model_name))
    preprocess(model)

    # Translate the model to Java code.
    render(model, model_folder)


if __name__ == '__main__':
    args = []
    for i in range(1, len(sys.argv)):
        args.append(sys.argv[i])
    main(args)

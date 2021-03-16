# Import the necessary libraries.
import argparse
import os

import settings
from libraries.slcolib import *
from preprocessing.grouping_annotations_smt import annotate_decision_groupings as annotate_decision_groupings_smt
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
    annotate_decision_groupings_smt(model)


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
    # Define the arguments that the program supports.
    parser = argparse.ArgumentParser(description="Transform an SLCO 2.0 model to a Java program")
    parser.add_argument("-c", nargs="?", type=int, const=10000, default=0, required=False,
                        help="produce a transition counter in the code, to make program executions finite")
    parser.add_argument("-t", nargs="?", type=int, const=60, default=0, required=False,
                        help="add a timer to the code, to make program executions finite (in seconds, default: 60s)")
    parser.add_argument("-nds", action='store_true',
                        help="disable deterministic structures")
    parser.add_argument("-lock_fairness", action='store_true',
                        help="enable fairness of locks")
    parser.add_argument("-v", action='store_true',
                        help="enable verbose debug prints")
    parser.add_argument("-pc", action='store_true',
                        help="add the performance counters")
    parser.add_argument("model",
                        help="The SLCO 2.0 model to be converted to a Java program.")

    # Parse the parameters and save the settings.
    settings.init(parser.parse_args(_args))

    # Read the model and preprocess it.
    model = read_SLCO_model(os.path.join(settings.model_folder, settings.model_name))
    preprocess(model)

    # Translate the model to Java code.
    render(model, settings.model_folder)


if __name__ == '__main__':
    args = []
    for i in range(1, len(sys.argv)):
        args.append(sys.argv[i])
    main(args)

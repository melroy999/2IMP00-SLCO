import pickle
import jinja2
import numpy
from statistics import mean, median, stdev, variance

with_fairness = False
if with_fairness:
    with open('results_fairness.pkl', 'rb') as f:  # Python 3: open(..., 'rb')
        test_statistics = pickle.load(f)
else:
    with open('results_no_fairness.pkl', 'rb') as f:  # Python 3: open(..., 'rb')
        test_statistics = pickle.load(f)


def calculate_aggregate_data(measurement, entries):
    measurement["sum"] = [sum(v[i] for v in entries) for i in range(0, 4)]
    measurement["mean"] = [mean(v[i] for v in entries) for i in range(0, 4)]
    measurement["max"] = [max(v[i] for v in entries) for i in range(0, 4)]
    measurement["min"] = [min(v[i] for v in entries) for i in range(0, 4)]
    measurement["median"] = [median(v[i] for v in entries) for i in range(0, 4)]
    measurement["stdev"] = [stdev(v[i] for v in entries) for i in range(0, 4)]
    measurement["variance"] = [variance(v[i] for v in entries) for i in range(0, 4)]
    measurement["n"] = len(entries)
    measurement["p25"] = [numpy.percentile(numpy.array([v[i] for v in entries]), 25) for i in range(0, 4)]
    measurement["p75"] = [numpy.percentile(numpy.array([v[i] for v in entries]), 75) for i in range(0, 4)]


# Process the data.
aggregate_data = {"DET": dict(), "N_DET": dict()}
for test_type in ["DET", "N_DET"]:
    for model, data in test_statistics[test_type].items():
        # Find the state machines that are part of the model.
        measure_points = sorted(data[0].keys())

        # Gather aggregate data such as the mean, std, etc.
        aggregate_model_data = {
            "entries": list(),
            "state_machines": dict(),
            "states": dict()
        }
        for target in measure_points:
            target_type = "state_machines" if len(target.split(".")) == 2 else "states"
            target_name = ".".join(target.split(".")[1:])
            aggregate_model_data[target_type][target_name] = {
                "entries": list()
            }
        for entry in data:
            aggregate_model_data["entries"].append([0, 0, 0, 0])
            last_element = aggregate_model_data["entries"][-1]
            for target, measurements in entry.items():
                target_type = "state_machines" if len(target.split(".")) == 2 else "states"
                target_name = ".".join(target.split(".")[1:])

                # noinspection PyTypeChecker
                aggregate_model_data[target_type][target_name]["entries"].append(measurements)

                if target_type == "state_machines":
                    for i in range(0, 2):
                        last_element[i] += measurements[i]
                    last_element[3] = max(last_element[3], measurements[3])

            # Recalculate the success ratio.
            last_element[2] = last_element[0] / last_element[1]

        # Calculate the statistics for each measure point.
        for _, measurements in aggregate_model_data["state_machines"].items():
            calculate_aggregate_data(measurements, measurements["entries"])
        for _, measurements in aggregate_model_data["states"].items():
            calculate_aggregate_data(measurements, measurements["entries"])
        calculate_aggregate_data(aggregate_model_data, aggregate_model_data["entries"])
        aggregate_data[test_type][model] = aggregate_model_data


# Group the models by test suites.
group_to_models = {
    "CounterDistributorExact": ["CounterDistributorExact%s" % (i + 1) for i in range(0, 10)],
    "CounterDistributorExactStress": ["CounterDistributorExactStress%s" % (i + 1) for i in range(0, 10)],
    "Elevator": ["dve_elevator2_%s" % (i + 1) for i in range(0, 3)],
    "Telephony": ["dve_telephony_%s" % (i + 1) for i in range(0, 8)],
}
group_mappings = {
    **{"CounterDistributorExact%s" % (i + 1): "CounterDistributorExact" for i in range(0, 10)},
    **{"CounterDistributorExactStress%s" % (i + 1): "CounterDistributorExactStress" for i in range(0, 10)},
    **{"dve_elevator2_%s" % (i + 1): "Elevator" for i in range(0, 3)},
    **{"dve_telephony_%s" % (i + 1): "Telephony" for i in range(0, 8)},
}
aggregate_data_groups = {
    "CounterDistributorExact": {"DET": dict(), "N_DET": dict()},
    "CounterDistributorExactStress": {"DET": dict(), "N_DET": dict()},
    "Elevator": {"DET": dict(), "N_DET": dict()},
    "Telephony": {"DET": dict(), "N_DET": dict()},
}
for model, det_data in aggregate_data["DET"].items():
    n_det_data = aggregate_data["N_DET"][model]
    target_group = group_mappings[model]
    aggregate_data_groups[target_group]["DET"][model] = det_data
    aggregate_data_groups[target_group]["N_DET"][model] = n_det_data


# Initialize the template engine.
env = jinja2.Environment(
    loader=jinja2.FileSystemLoader('jinja2_templates'),
    trim_blocks=True,
    lstrip_blocks=True,
    extensions=['jinja2.ext.loopcontrols', 'jinja2.ext.do']
)
latex_plot_template = env.get_template('report/plot.jinja2template')
group_plot_nr_of_successful_transitions_template = env.get_template(
    'report/group_plot_nr_of_successful_transitions.jinja2template'
)
group_plot_success_ratio_template = env.get_template(
    'report/group_plot_success_ratio.jinja2template'
)
group_plot_nr_of_successful_transitions_comparison_template = env.get_template(
    'report/group_plot_nr_of_successful_transitions_comparison.jinja2template'
)


def add_group_plot_entries(
        group_name,
        view_model,
        measurement,
        confidence_interval_error,
        target_selector=lambda target_data: target_data
):
    # Add the data to plot.
    group_data = aggregate_data_groups[group_name]
    for decision_type in ["DET", "N_DET"]:
        for i, target_model in enumerate(group_to_models[group_name]):
            target_data = target_selector(group_data[decision_type][target_model])

            # Use the stdev for the errors bars if true. Otherwise, use the min and max.
            if confidence_interval_error:
                view_model[decision_type].append("(%s, %s) +- (0, %s)" % (
                    i + 1,
                    target_data["mean"][measurement],
                    target_data["stdev"][measurement],
                ))
            else:
                view_model[decision_type].append("(%s, %s) += (0, %s) -= (0, %s)" % (
                    i + 1,
                    target_data["mean"][measurement],
                    target_data["max"][measurement] - target_data["mean"][measurement],
                    target_data["mean"][measurement] - target_data["min"][measurement],
                ))


def render_nr_of_successful_transitions_group_plot(
        group_name,
        confidence_interval_error=True,
        n=20,
        t=30,
        step=60000000,
        pins=5,
        model_suffix=None,
        output_file_name=None,
):
    # A view model for the bar plot.
    view_model = {
        "DET": list(),
        "N_DET": list(),
        "base_model": group_name,
        "n": n,
        "t": t,
        "max": (pins + 1) * step,
        "step": step,
        "step_max": pins * step,
        "model_suffix": model_suffix,
        "is_fair": with_fairness
    }
    if model_suffix:
        view_model["label"] = "model:%s.%s:nr_of_successful_transitions" % (group_name, model_suffix)
    else:
        view_model["label"] = "model:%s:nr_of_successful_transitions" % group_name

    # Add the data to plot.
    if not model_suffix:
        add_group_plot_entries(group_name, view_model, 0, confidence_interval_error)
    else:
        target_extension = model_suffix.split(".")
        if len(target_extension) == 1:
            add_group_plot_entries(
                group_name,
                view_model,
                0,
                confidence_interval_error,
                target_selector=lambda target_data: target_data["state_machines"][target_extension[0]]
            )
        elif len(target_extension) == 2:
            add_group_plot_entries(
                group_name,
                view_model,
                0,
                confidence_interval_error,
                target_selector=lambda target_data:
                    target_data["states"]["%s.%s" % (target_extension[0], target_extension[1])]
            )

    if output_file_name:
        with open(output_file_name, "w") as output_file:
            output_file.write(group_plot_nr_of_successful_transitions_template.render(model=view_model))
    else:
        print(group_plot_nr_of_successful_transitions_template.render(model=view_model))


def render_success_ratio_group_plot(
        group_name,
        confidence_interval_error=True,
        n=20,
        t=30,
        step=0.2,
        pins=5,
        model_suffix=None,
        output_file_name=None,
):
    # A view model for the bar plot.
    view_model = {
        "DET": list(),
        "N_DET": list(),
        "base_model": group_name,
        "n": n,
        "t": t,
        "max": (pins + 1) * step,
        "step": step,
        "step_max": pins * step,
        "model_suffix": model_suffix,
        "is_fair": with_fairness
    }
    if model_suffix:
        view_model["label"] = "model:%s.%s:success_ratio" % (group_name, model_suffix)
    else:
        view_model["label"] = "model:%s:success_ratio" % group_name

    # Add the data to plot.
    if not model_suffix:
        add_group_plot_entries(group_name, view_model, 2, confidence_interval_error)
    else:
        target_extension = model_suffix.split(".")
        if len(target_extension) == 1:
            add_group_plot_entries(
                group_name,
                view_model,
                2,
                confidence_interval_error,
                target_selector=lambda target_data: target_data["state_machines"][target_extension[0]]
            )
        elif len(target_extension) == 2:
            add_group_plot_entries(
                group_name,
                view_model,
                2,
                confidence_interval_error,
                target_selector=lambda target_data:
                    target_data["states"]["%s.%s" % (target_extension[0], target_extension[1])]
            )

    if output_file_name:
        with open(output_file_name, "w") as output_file:
            output_file.write(group_plot_success_ratio_template.render(model=view_model))
    else:
        print(group_plot_success_ratio_template.render(model=view_model))


def render_nr_of_successful_transitions_comparison_plot(
        target_models,
        confidence_interval_error=True,
        n=20,
        t=30,
        step=30000000,
        pins=5,
        model_abbreviations=None,
        bar_width=None,
        output_file_name=None,
):
    if not model_abbreviations:
        model_abbreviations = {target_model: target_model for target_model in target_models}

    # A view model for the bar plot.
    view_model = {
        "DET": list(),
        "N_DET": list(),
        "x_values": ", ".join(model_abbreviations[target_model] for target_model in target_models),
        "target_models": "%s and %s" % (", ".join(target_models[:-1]), target_models[-1]),
        "n": n,
        "t": t,
        "max": (pins + 1) * step,
        "step": step,
        "step_max": pins * step,
        "bar_width": bar_width,
        "label": "model:%s:nr_of_successful_transitions_comparison" % ":".join(
            model_abbreviations[target_model] for target_model in target_models
        ),
        "is_fair": with_fairness
    }

    for target_model in target_models:
        for decision_type in ["DET", "N_DET"]:
            model_split = target_model.split(".")
            model_name = model_split[0]
            target_machine, target_state = None, None
            if len(model_split) > 1:
                target_machine = model_split[1]
            elif len(model_split) > 2:
                target_state = model_split[2]

            target_data = aggregate_data[decision_type][model_name]
            if target_machine and target_state:
                target_data = target_data["states"]["%s.%s" % (target_machine, target_state)]
            elif target_machine:
                target_data = target_data["state_machines"][target_machine]

            if confidence_interval_error:
                view_model[decision_type].append("(%s, %s) +- (0, %s)" % (
                    model_abbreviations[target_model] if model_abbreviations else target_model,
                    target_data["mean"][0],
                    target_data["stdev"][0],
                ))
            else:
                view_model[decision_type].append("(%s, %s) += (0, %s) -= (0, %s)" % (
                    model_abbreviations[target_model] if model_abbreviations else target_model,
                    target_data["mean"][0],
                    target_data["max"][0] - target_data["mean"][0],
                    target_data["mean"][0] - target_data["min"][0],
                ))

    if output_file_name:
        with open(output_file_name, "w") as output_file:
            output_file.write(group_plot_nr_of_successful_transitions_comparison_template.render(model=view_model))
    else:
        print(group_plot_nr_of_successful_transitions_comparison_template.render(model=view_model))


if with_fairness:
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExact", step=3000000,
        output_file_name="plots/fair/CounterDistributorExact_nr_of_st_group_plot.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExact",
        output_file_name="plots/fair/CounterDistributorExact_nr_of_sr_group_plot.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExact", model_suffix="Distributor.P", step=1500000,
        output_file_name="plots/fair/CounterDistributorExact_nr_of_st_group_plot.Distributor.P.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExact", model_suffix="Distributor.P",
        output_file_name="plots/fair/CounterDistributorExact_nr_of_sr_group_plot.Distributor.P.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExact", model_suffix="Counter.C", step=1500000,
        output_file_name="plots/fair/CounterDistributorExact_nr_of_st_group_plot.Counter.C.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExact", model_suffix="Counter.C",
        output_file_name="plots/fair/CounterDistributorExact_nr_of_sr_group_plot.Counter.C.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExactStress", step=3000000,
        output_file_name="plots/fair/CounterDistributorExactStress_nr_of_st_group_plot.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExactStress",
        output_file_name="plots/fair/CounterDistributorExactStress_nr_of_sr_group_plot.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExactStress", model_suffix="Distributor.P", step=1500000,
        output_file_name="plots/fair/CounterDistributorExactStress_nr_of_st_group_plot.Distributor.P.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExactStress", model_suffix="Distributor.P",
        output_file_name="plots/fair/CounterDistributorExactStress_nr_of_sr_group_plot.Distributor.P.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExactStress", model_suffix="Counter.C", step=1500000,
        output_file_name="plots/fair/CounterDistributorExactStress_nr_of_st_group_plot.Counter.C.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExactStress", model_suffix="Counter.C",
        output_file_name="plots/fair/CounterDistributorExactStress_nr_of_sr_group_plot.Counter.C.tex"
    )
    render_nr_of_successful_transitions_comparison_plot(
        [
            "CounterDistributorExact10",
            "CounterDistributorExact10.Counter",
            "CounterDistributorExact10.Distributor",
            "CounterDistributorExactStress10",
            "CounterDistributorExactStress10.Counter",
            "CounterDistributorExactStress10.Distributor",
        ],
        model_abbreviations={
            "CounterDistributorExact10": "CDE.10",
            "CounterDistributorExact10.Counter": "CDE.10.Counter",
            "CounterDistributorExact10.Distributor": "CDE.10.Distributor",
            "CounterDistributorExactStress10": "CDES.10",
            "CounterDistributorExactStress10.Counter": "CDES.10.Counter",
            "CounterDistributorExactStress10.Distributor": "CDES.10.Distributor",
        },
        step=3000000,
        bar_width="0.6cm",
        output_file_name="plots/fair/CounterDistributorExact10_CounterDistributorExactStress10_st_comparison.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "Elevator", step=5000000,
        output_file_name="plots/fair/Elevator_nr_of_st_group_plot.tex"
    )
    render_nr_of_successful_transitions_comparison_plot(
        [
            "dve_elevator2_1.cabin",
            "dve_elevator2_1.environment",
            "dve_elevator2_1.controller",
            "dve_elevator2_2.cabin",
            "dve_elevator2_2.environment",
            "dve_elevator2_2.controller",
            "dve_elevator2_3.cabin",
            "dve_elevator2_3.environment",
            "dve_elevator2_3.controller",
        ],
        model_abbreviations={
            "dve_elevator2_1.cabin": "Elevator.2.1.Cabin",
            "dve_elevator2_1.environment": "Elevator.2.1.Environment",
            "dve_elevator2_1.controller": "Elevator.2.1.Controller",
            "dve_elevator2_2.cabin": "Elevator.2.2.Cabin",
            "dve_elevator2_2.environment": "Elevator.2.2.Environment",
            "dve_elevator2_2.controller": "Elevator.2.2.Controller",
            "dve_elevator2_3.cabin": "Elevator.2.3.Cabin",
            "dve_elevator2_3.environment": "Elevator.2.3.Environment",
            "dve_elevator2_3.controller": "Elevator.2.3.Controller",
        },
        step=14000000,
        output_file_name="plots/fair/Elevator_state_comparison.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "Telephony", step=250000000,
        output_file_name="plots/fair/Telephony_nr_of_st_group_plot.tex"
    )
else:
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExact", step=100000000,
        output_file_name="plots/unfair/CounterDistributorExact_nr_of_st_group_plot.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExact",
        output_file_name="plots/unfair/CounterDistributorExact_nr_of_sr_group_plot.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExact", model_suffix="Distributor.P", step=60000000,
        output_file_name="plots/unfair/CounterDistributorExact_nr_of_st_group_plot.Distributor.P.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExact", model_suffix="Distributor.P",
        output_file_name="plots/unfair/CounterDistributorExact_nr_of_sr_group_plot.Distributor.P.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExact", model_suffix="Counter.C", step=70000000,
        output_file_name="plots/unfair/CounterDistributorExact_nr_of_st_group_plot.Counter.C.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExact", model_suffix="Counter.C",
        output_file_name="plots/unfair/CounterDistributorExact_nr_of_sr_group_plot.Counter.C.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExactStress", step=80000000,
        output_file_name="plots/unfair/CounterDistributorExactStress_nr_of_st_group_plot.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExactStress",
        output_file_name="plots/unfair/CounterDistributorExactStressStress_nr_of_sr_group_plot.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExactStress", model_suffix="Distributor.P", step=40000000,
        output_file_name="plots/unfair/CounterDistributorExactStress_nr_of_st_group_plot.Distributor.P.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExactStress", model_suffix="Distributor.P",
        output_file_name="plots/unfair/CounterDistributorExactStress_nr_of_sr_group_plot.Distributor.P.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "CounterDistributorExactStress", model_suffix="Counter.C", step=40000000,
        output_file_name="plots/unfair/CounterDistributorExactStress_nr_of_st_group_plot.Counter.C.tex"
    )
    render_success_ratio_group_plot(
        "CounterDistributorExactStress", model_suffix="Counter.C",
        output_file_name="plots/unfair/CounterDistributorExactStress_nr_of_sr_group_plot.Counter.C.tex"
    )
    render_nr_of_successful_transitions_comparison_plot(
        [
            "CounterDistributorExact10",
            "CounterDistributorExact10.Counter",
            "CounterDistributorExact10.Distributor",
            "CounterDistributorExactStress10",
            "CounterDistributorExactStress10.Counter",
            "CounterDistributorExactStress10.Distributor",
        ],
        model_abbreviations={
            "CounterDistributorExact10": "CDE.10",
            "CounterDistributorExact10.Counter": "CDE.10.Counter",
            "CounterDistributorExact10.Distributor": "CDE.10.Distributor",
            "CounterDistributorExactStress10": "CDES.10",
            "CounterDistributorExactStress10.Counter": "CDES.10.Counter",
            "CounterDistributorExactStress10.Distributor": "CDES.10.Distributor",
        },
        step=100000000,
        bar_width="0.6cm",
        output_file_name="plots/unfair/CounterDistributorExact10_CounterDistributorExactStress10_st_comparison.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "Elevator", step=20000000,
        output_file_name="plots/unfair/Elevator_nr_of_st_group_plot.tex"
    )
    render_nr_of_successful_transitions_comparison_plot(
        [
            "dve_elevator2_1.cabin",
            "dve_elevator2_1.environment",
            "dve_elevator2_1.controller",
            "dve_elevator2_2.cabin",
            "dve_elevator2_2.environment",
            "dve_elevator2_2.controller",
            "dve_elevator2_3.cabin",
            "dve_elevator2_3.environment",
            "dve_elevator2_3.controller",
        ],
        model_abbreviations={
            "dve_elevator2_1.cabin": "Elevator.2.1.Cabin",
            "dve_elevator2_1.environment": "Elevator.2.1.Environment",
            "dve_elevator2_1.controller": "Elevator.2.1.Controller",
            "dve_elevator2_2.cabin": "Elevator.2.2.Cabin",
            "dve_elevator2_2.environment": "Elevator.2.2.Environment",
            "dve_elevator2_2.controller": "Elevator.2.2.Controller",
            "dve_elevator2_3.cabin": "Elevator.2.3.Cabin",
            "dve_elevator2_3.environment": "Elevator.2.3.Environment",
            "dve_elevator2_3.controller": "Elevator.2.3.Controller",
        },
        step=14000000,
        output_file_name="plots/unfair/Elevator_state_comparison.tex"
    )
    render_nr_of_successful_transitions_group_plot(
        "Telephony", step=160000000,
        output_file_name="plots/unfair/Telephony_nr_of_st_group_plot.tex"
    )

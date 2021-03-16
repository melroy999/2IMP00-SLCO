import pickle
import jinja2
import numpy
from statistics import mean, median, stdev, variance

with open('objs.pkl', 'rb') as f:  # Python 3: open(..., 'rb')
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
    "Elevator": ["elevator2.%s" % (i + 1) for i in range(0, 3)],
    "Telephony": ["telephony.%s" % (i + 1) for i in range(0, 9)],
}
group_mappings = {
    **{"CounterDistributorExact%s" % (i + 1): "CounterDistributorExact" for i in range(0, 10)},
    **{"CounterDistributorExactStress%s" % (i + 1): "CounterDistributorExactStress" for i in range(0, 10)},
    **{"elevator2.%s" % (i + 1): "Elevator" for i in range(0, 3)},
    **{"telephony.%s" % (i + 1): "Telephony" for i in range(0, 9)},
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
        _max=358000000,
        step=60000000,
        step_max=300000000,
        model_suffix=None,
):
    # A view model for the bar plot.
    view_model = {
        "DET": list(),
        "N_DET": list(),
        "base_model": group_name,
        "n": n,
        "t": t,
        "max": _max,
        "step": step,
        "step_max": step_max,
        "model_suffix": model_suffix
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

    print(group_plot_nr_of_successful_transitions_template.render(model=view_model))


def render_success_ratio_group_plot(
        group_name,
        confidence_interval_error=True,
        n=20,
        t=30,
        model_suffix=None,
):
    # A view model for the bar plot.
    view_model = {
        "DET": list(),
        "N_DET": list(),
        "base_model": group_name,
        "n": n,
        "t": t,
        "max": 1.2,
        "step": 0.2,
        "step_max": 1,
        "model_suffix": model_suffix
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

    print(group_plot_success_ratio_template.render(model=view_model))


render_nr_of_successful_transitions_group_plot(
    "CounterDistributorExact", _max=358000000, step_max=300000000, step=60000000
)
render_success_ratio_group_plot("CounterDistributorExact")
render_nr_of_successful_transitions_group_plot(
    "CounterDistributorExact", model_suffix="Distributor.P", _max=179000000, step_max=150000000, step=25000000
)
render_success_ratio_group_plot("CounterDistributorExact", model_suffix="Distributor.P")
render_nr_of_successful_transitions_group_plot(
    "CounterDistributorExactStress", _max=240000000, step_max=200000000, step=40000000
)
render_success_ratio_group_plot("CounterDistributorExactStress")
render_nr_of_successful_transitions_group_plot(
    "CounterDistributorExactStress", model_suffix="Distributor.P", _max=120000000, step_max=100000000, step=20000000
)
render_success_ratio_group_plot("CounterDistributorExactStress", model_suffix="Distributor.P")
exit(0)


def render_plot(
        model_names,
        target_measurement,
        model_abbreviations=lambda name: name,
        target=lambda test_type, name: aggregate_data[test_type][name],
        title=None,
        xlabel=None,
        ylabel=None
):
    view_model = {
        "names": model_names,
        "DET": list(),
        "N_DET": list(),
        "title": title,
        "xlabel": xlabel,
        "ylabel": ylabel,
    }
    view_model["names_csl"] = ", ".join(model_abbreviations(name) for name in view_model["names"])
    for name in view_model["names"]:
        for test_type in ["DET", "N_DET"]:
            target_data = target(test_type, name)
            view_model[test_type].append("(%s, %s) += (0, %s) -= (0, %s)" % (
                model_abbreviations(name),
                target_data["mean"][target_measurement],
                target_data["max"][target_measurement] - target_data["mean"][target_measurement],
                target_data["mean"][target_measurement] - target_data["min"][target_measurement],
            ))
    print(latex_plot_template.render(model=view_model))
    print()


def render_exact():
    render_plot(
        ["CounterDistributorExact%s" % i for i in range(1, 11)],
        0,
        model_abbreviations=lambda name: name.replace("CounterDistributorExact", "CDE"),
        target=lambda test_type, name: aggregate_data[test_type][name],
        title="Number of successful transitions for the CounterDistributorExact test suite",
        xlabel="Variants of the CounterDistributorExact state machine",
        ylabel="Number of successful transitions"
    )

    render_plot(
        ["CounterDistributorExact%s" % i for i in range(1, 11)],
        2,
        model_abbreviations=lambda name: name.replace("CounterDistributorExact", "CDE"),
        target=lambda test_type, name: aggregate_data[test_type][name],
        title="Success ratio for the transitions in the CounterDistributorExact test suite",
        xlabel="Variants of the CounterDistributorExact state machine",
        ylabel="Successful transitions/total transitions"
    )

    render_plot(
        ["CounterDistributorExact%s" % i for i in range(1, 11)],
        0,
        model_abbreviations=lambda name: name.replace("CounterDistributorExact", "CDE"),
        target=lambda test_type, name: aggregate_data[test_type][name]["states"]["CounterDistributorExact.Distributor.P"],
        title="Number of successful transitions for state P in the CounterDistributorExact test suite",
        xlabel="Variants of the CounterDistributorExact state machine",
        ylabel="Number of successful transitions"
    )

    render_plot(
        ["CounterDistributorExact%s" % i for i in range(1, 11)],
        2,
        model_abbreviations=lambda name: name.replace("CounterDistributorExact", "CDE"),
        target=lambda test_type, name: aggregate_data[test_type][name]["states"]["CounterDistributorExact.Distributor.P"],
        title="Success ratio for the transitions in state P of the CounterDistributorExact test suite",
        xlabel="Variants of the CounterDistributorExact state machine",
        ylabel="Successful transitions/total transitions"
    )

    render_plot(
        ["CounterDistributorExact%s" % i for i in range(1, 11)],
        0,
        model_abbreviations=lambda name: name.replace("CounterDistributorExact", "CDE"),
        target=lambda test_type, name: aggregate_data[test_type][name]["states"]["CounterDistributorExact.Counter.C"],
        title="Number of successful transitions for state C in the CounterDistributorExact test suite",
        xlabel="Variants of the CounterDistributorExact state machine",
        ylabel="Number of successful transitions"
    )

    render_plot(
        ["CounterDistributorExact%s" % i for i in range(1, 11)],
        2,
        model_abbreviations=lambda name: name.replace("CounterDistributorExact", "CDE"),
        target=lambda test_type, name: aggregate_data[test_type][name]["states"]["CounterDistributorExact.Counter.C"],
        title="Success ratio for the transitions in state C of the CounterDistributorExact test suite",
        xlabel="Variants of the CounterDistributorExact state machine",
        ylabel="Successful transitions/total transitions"
    )


def render_exact_stress():
    render_plot(
        ["CounterDistributorExactStress%s" % i for i in range(1, 11)],
        0,
        model_abbreviations=lambda name: name.replace("CounterDistributorExactStress", "CDES"),
        target=lambda test_type, name: aggregate_data[test_type][name],
        title="Number of successful transitions for the CounterDistributorExactStress test suite",
        xlabel="Variants of the CounterDistributorExactStress state machine",
        ylabel="Number of successful transitions"
    )

    render_plot(
        ["CounterDistributorExactStress%s" % i for i in range(1, 11)],
        2,
        model_abbreviations=lambda name: name.replace("CounterDistributorExactStress", "CDES"),
        target=lambda test_type, name: aggregate_data[test_type][name],
        title="Success ratio for the transitions in the CounterDistributorExactStress test suite",
        xlabel="Variants of the CounterDistributorExactStress state machine",
        ylabel="Successful transitions/total transitions"
    )

    render_plot(
        ["CounterDistributorExactStress%s" % i for i in range(1, 11)],
        0,
        model_abbreviations=lambda name: name.replace("CounterDistributorExactStress", "CDES"),
        target=lambda test_type, name: aggregate_data[test_type][name]["states"]["CounterDistributorExactStress.Distributor.P"],
        title="Number of successful transitions for state P in the CounterDistributorExactStress test suite",
        xlabel="Variants of the CounterDistributorExactStress state machine",
        ylabel="Number of successful transitions"
    )

    render_plot(
        ["CounterDistributorExactStress%s" % i for i in range(1, 11)],
        2,
        model_abbreviations=lambda name: name.replace("CounterDistributorExactStress", "CDES"),
        target=lambda test_type, name: aggregate_data[test_type][name]["states"]["CounterDistributorExactStress.Distributor.P"],
        title="Success ratio for the transitions in state P of the CounterDistributorExactStress test suite",
        xlabel="Variants of the CounterDistributorExactStress state machine",
        ylabel="Successful transitions/total transitions"
    )

    render_plot(
        ["CounterDistributorExactStress%s" % i for i in range(1, 11)],
        0,
        model_abbreviations=lambda name: name.replace("CounterDistributorExactStress", "CDES"),
        target=lambda test_type, name: aggregate_data[test_type][name]["states"]["CounterDistributorExactStress.Counter.C"],
        title="Number of successful transitions for state C in the CounterDistributorExactStress test suite",
        xlabel="Variants of the CounterDistributorExactStress state machine",
        ylabel="Number of successful transitions"
    )

    render_plot(
        ["CounterDistributorExactStress%s" % i for i in range(1, 11)],
        2,
        model_abbreviations=lambda name: name.replace("CounterDistributorExactStress", "CDES"),
        target=lambda test_type, name: aggregate_data[test_type][name]["states"]["CounterDistributorExactStress.Counter.C"],
        title="Success ratio for the transitions in state C of the CounterDistributorExactStress test suite",
        xlabel="Variants of the CounterDistributorExactStress state machine",
        ylabel="Successful transitions/total transitions"
    )

# render_exact()
# render_exact_stress()

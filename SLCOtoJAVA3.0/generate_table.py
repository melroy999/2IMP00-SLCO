import jinja2

from preprocess_experiment_data import gather_data

# Initialize the template engine.
env = jinja2.Environment(
    loader=jinja2.FileSystemLoader("jinja2_templates"),
    trim_blocks=True,
    lstrip_blocks=True,
    extensions=["jinja2.ext.loopcontrols", "jinja2.ext.do"]
)
latex_table_template = env.get_template("report/result_table.jinja2template")
latex_table_2_template = env.get_template("report/result_table_2.jinja2template")

# Import all the data.
aggregate_data = gather_data(fair="results_fairness_telephony.pkl", unfair="results_no_fairness_telephony.pkl")


def to_scientific_notation(v):
    float_str = "{0:.2e}".format(v)
    if "e" in float_str:
        base, exponent = float_str.split("e")
        if exponent in ["+00"]:
            return r"${0}$".format(base)
        elif exponent in ["-01"]:
            return "${0:.2f}$".format(v)
        else:
            return r"${0} \cdot 10^{{{1}}}$".format(base, int(exponent))
    else:
        return float_str


def generate_fairness_comparison_table(
        target_models, target_model_name, label, output_file_name=None, table_widths=None
):
    if table_widths is None:
        table_widths = ["1.6cm", "1cm", "1.6cm", "1cm", "1.6cm", "1cm", "1.6cm", "1cm"]
    view_model = {
        "n": 20,
        "t": 30,
        "label": "%s:lock_type_comparison_table" % label,
        "entries": list(),
        "target_model": target_model_name,
        "table_col_def": "{|X||%s||%s|}" % (
            "|".join("C{%s}" % v for v in table_widths[:4]),
            "|".join("C{%s}" % v for v in table_widths[4:])
        )
    }

    for model_name, model_abbreviation in target_models.items():
        model_split = model_name.split(".")
        if len(model_split) == 1:
            def target(data): return data[model_split[0]]
        elif len(model_split) == 2:
            def target(data): return data[model_split[0]]["state_machines"][model_split[1]]
        else:
            def target(data): return data[model_split[0]]["states"]["%s.%s" % (model_split[1], model_split[2])]

        try:
            unfair_det_mean = target(aggregate_data["UNFAIR"]["DET"])
            unfair_n_det_mean = target(aggregate_data["UNFAIR"]["N_DET"])
            fair_det_mean = target(aggregate_data["FAIR"]["DET"])
            fair_n_det_mean = target(aggregate_data["FAIR"]["N_DET"])
        except KeyError:
            continue

        data_entry = "%s & %s \\\\" % (model_abbreviation, " & ".join(to_scientific_notation(v) for v in [
            unfair_det_mean["mean"][0],
            unfair_det_mean["mean"][2],
            unfair_n_det_mean["mean"][0],
            unfair_n_det_mean["mean"][2],
            fair_det_mean["mean"][0],
            fair_det_mean["mean"][2],
            fair_n_det_mean["mean"][0],
            fair_n_det_mean["mean"][2],
        ]))

        view_model["entries"].append(data_entry)

    if output_file_name:
        with open(output_file_name, "w") as output_file:
            output_file.write(latex_table_2_template.render(model=view_model))
    else:
        print(latex_table_2_template.render(model=view_model))


def generate_result_table(
        target_models, target_model_name, label, lock_setting="UNFAIR", output_file_name=None, table_widths=None
):
    if table_widths is None:
        table_widths = ["1.6cm", "1.6cm", "1cm", "1cm", "1.6cm", "1.6cm", "1cm", "1.6cm"]
    view_model = {
        "n": 20,
        "t": 30,
        "label": "%s:%s:result_table" % (lock_setting, label),
        "entries": list(),
        "is_fair": lock_setting == "FAIR",
        "target_model": target_model_name,
        "table_col_def": "{|X||%s||%s|}" % (
            "|".join("C{%s}" % v for v in table_widths[:4]),
            "|".join("C{%s}" % v for v in table_widths[4:])
        )
    }

    for model_name, model_abbreviation in target_models.items():
        model_split = model_name.split(".")
        if len(model_split) == 1:
            def target(data): return data[model_split[0]]
        elif len(model_split) == 2:
            def target(data): return data[model_split[0]]["state_machines"][model_split[1]]
        else:
            def target(data): return data[model_split[0]]["states"]["%s.%s" % (model_split[1], model_split[2])]

        try:
            det_data = target(aggregate_data[lock_setting]["DET"])
            n_det_data = target(aggregate_data[lock_setting]["N_DET"])
        except KeyError:
            continue

        data_entry = "%s & %s \\\\" % (model_abbreviation, " & ".join(to_scientific_notation(v) for v in [
            det_data["mean"][0],
            det_data["stdev"][0],
            det_data["mean"][2],
            det_data["stdev"][2],
            n_det_data["mean"][0],
            n_det_data["stdev"][0],
            n_det_data["mean"][2],
            n_det_data["stdev"][2],
        ]))

        view_model["entries"].append(data_entry)

    if output_file_name:
        with open(output_file_name, "w") as output_file:
            output_file.write(latex_table_template.render(model=view_model))
    else:
        print(latex_table_template.render(model=view_model))


# target_models = {
#     **{"CounterDistributorExact%s" % (i + 1): "CDE.%s" % (i + 1) for i in range(0, 10)},
#     **{"CounterDistributorExact%s.Distributor.P" % (i + 1): "CDE.%s.Distributor.P" % (i + 1) for i in range(0, 10)},
#     **{"CounterDistributorExact%s.Counter.C" % (i + 1): "CDE.%s.Counter.C" % (i + 1) for i in range(0, 10)},
# }

target_models = {}
for i in range(0, 10):
    target_models["CounterDistributorExact%s" % (i + 1)] = "CDE.%s" % (i + 1)
    target_models["CounterDistributorExact%s.Distributor.P" % (i + 1)] = "$\\vartriangleright$ CDE.%s.Distributor.P" % (i + 1)
    target_models["CounterDistributorExact%s.Counter.C" % (i + 1)] = "$\\vartriangleright$ CDE.%s.Counter.C" % (i + 1)


generate_result_table(
    target_models, "CounterDistributorExact.\\texttt{i}", "CounterDistributorExact",
    output_file_name="tables/CounterDistributorExact_unfair_table.tex",
    table_widths=["1.6cm", "1.6cm", "1cm", "1cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm"]
)
generate_result_table(
    target_models, "CounterDistributorExact.\\texttt{i}", "CounterDistributorExact", lock_setting="FAIR",
    output_file_name="tables/CounterDistributorExact_fair_table.tex"
)
generate_fairness_comparison_table(
    target_models, "CounterDistributorExact.\\texttt{i}", "CounterDistributorExact",
    output_file_name="tables/CounterDistributorExact_summary_table.tex",
    table_widths=["1.6cm", "1cm", "1.6cm", "1.6cm", "1.6cm", "1cm", "1.6cm", "1cm"]
)

target_models = {}
for i in range(0, 10):
    target_models["CounterDistributorExactStress%s" % (i + 1)] = "CDES.%s" % (i + 1)
    target_models["CounterDistributorExactStress%s.Distributor.P" % (i + 1)] = "$\\vartriangleright$ CDES.%s.Distributor.P" % (i + 1)
    target_models["CounterDistributorExactStress%s.Counter.C" % (i + 1)] = "$\\vartriangleright$ CDES.%s.Counter.C" % (i + 1)

generate_result_table(
    target_models, "CounterDistributorExactStress.\\texttt{i}", "CounterDistributorExactStress",
    output_file_name="tables/CounterDistributorExactStress_unfair_table.tex"
)
generate_result_table(
    target_models, "CounterDistributorExactStress.\\texttt{i}", "CounterDistributorExactStress", lock_setting="FAIR",
    output_file_name="tables/CounterDistributorExactStress_fair_table.tex"
)
generate_fairness_comparison_table(
    target_models, "CounterDistributorExactStress.\\texttt{i}", "CounterDistributorExactStress",
    output_file_name="tables/CounterDistributorExactStress_summary_table.tex"
)

target_models = {}
for i in range(0, 3):
    target_models["dve_elevator2_%s" % (i + 1)] = "Elevator.2.%s" % (i + 1)
    target_models["dve_elevator2_%s.cabin.idle" % (i + 1)] = "$\\vartriangleright$ Elevator.2.%s.cabin.idle" % (i + 1)
    target_models["dve_elevator2_%s.cabin.mov" % (i + 1)] = "$\\vartriangleright$ Elevator.2.%s.cabin.mov" % (i + 1)
    target_models["dve_elevator2_%s.cabin.open" % (i + 1)] = "$\\vartriangleright$ Elevator.2.%s.cabin.open" % (i + 1)
    target_models["dve_elevator2_%s.controller.wait" % (i + 1)] = "$\\vartriangleright$ Elevator.2.%s.controller.wait" % (i + 1)
    target_models["dve_elevator2_%s.controller.work" % (i + 1)] = "$\\vartriangleright$ Elevator.2.%s.controller.work" % (i + 1)
    target_models["dve_elevator2_%s.controller.done" % (i + 1)] = "$\\vartriangleright$ Elevator.2.%s.controller.done" % (i + 1)
    target_models["dve_elevator2_%s.environment.read" % (i + 1)] = "$\\vartriangleright$ Elevator.2.%s.environment.read" % (i + 1)

generate_result_table(
    target_models, "Elevator.2.\\texttt{i}", "Elevator.2",
    output_file_name="tables/Elevator.2_unfair_table.tex",
    table_widths=["1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm"]
)
generate_result_table(
    target_models, "Elevator.2.\\texttt{i}", "Elevator.2", lock_setting="FAIR",
    output_file_name="tables/Elevator.2_fair_table.tex",
    table_widths=["1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm"]
)
generate_fairness_comparison_table(
    target_models, "Elevator.2.\\texttt{i}", "Elevator.2",
    output_file_name="tables/Elevator.2_summary_table.tex",
    table_widths=["1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm", "1.6cm"]
)

target_models = {}
for i in range(0, 8):
    target_models["dve_telephony_%s" % (i + 1)] = "Telephony.%s" % (i + 1)
    target_models["dve_telephony_%s.User_0" % (i + 1)] = "$\\vartriangleright$ Telephony.%s.User\\_0" % (i + 1)
    target_models["dve_telephony_%s.User_1" % (i + 1)] = "$\\vartriangleright$ Telephony.%s.User\\_1" % (i + 1)
    target_models["dve_telephony_%s.User_2" % (i + 1)] = "$\\vartriangleright$ Telephony.%s.User\\_2" % (i + 1)
    target_models["dve_telephony_%s.User_3" % (i + 1)] = "$\\vartriangleright$ Telephony.%s.User\\_3" % (i + 1)

generate_result_table(
    target_models, "Telephony.\\texttt{i}", "Telephony",
    output_file_name="tables/Telephony_unfair_table.tex",
    table_widths=["1.6cm", "1.6cm", "1.0cm", "1.8cm", "1.6cm", "1.6cm", "1.0cm", "1.6cm"]
)
generate_result_table(
    target_models, "Telephony.\\texttt{i}", "Telephony", lock_setting="FAIR",
    output_file_name="tables/Telephony_fair_table.tex",
    table_widths=["1.6cm", "1.6cm", "1.0cm", "1.6cm", "1.6cm", "1.6cm", "1.0cm", "1.6cm"]
)
generate_fairness_comparison_table(
    target_models, "Telephony.\\texttt{i}", "Telephony",
    output_file_name="tables/Telephony_summary_table.tex"
)


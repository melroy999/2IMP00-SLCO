import pickle
from statistics import mean, median, stdev, variance


def calculate_aggregate_data(measurement, entries):
    measurement["mean"] = [mean(v[i] for v in entries) for i in range(0, 4)]
    measurement["max"] = [max(v[i] for v in entries) for i in range(0, 4)]
    measurement["min"] = [min(v[i] for v in entries) for i in range(0, 4)]
    measurement["median"] = [median(v[i] for v in entries) for i in range(0, 4)]
    measurement["stdev"] = [stdev(v[i] for v in entries) for i in range(0, 4)]
    measurement["variance"] = [variance(v[i] for v in entries) for i in range(0, 4)]
    measurement["n"] = len(entries)


def process_data(test_statistics, output_target):
    # Process the data.
    for test_type in ["DET", "N_DET"]:
        output_target[test_type] = dict()
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
            output_target[test_type][model] = aggregate_model_data


def gather_data():
    with open("results_fairness.pkl", "rb") as f:
        test_statistics_fair = pickle.load(f)
    with open("results_no_fairness.pkl", "rb") as f:
        test_statistics_unfair = pickle.load(f)

    data = {"FAIR": dict(), "UNFAIR": dict()}
    process_data(test_statistics_fair, data["FAIR"])
    process_data(test_statistics_unfair, data["UNFAIR"])
    return data


if __name__ == "__main__":
    aggregate_data = gather_data()

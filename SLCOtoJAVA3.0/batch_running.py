import os
import pickle
import subprocess
from statistics import mean, median, stdev, variance
from subprocess import STDOUT, PIPE

from past.builtins import raw_input

import slco2java

txt = raw_input("use pickle data? (y/n): ")

if txt == "n":
    # We have tests for deterministic and non-deterministic versions.
    for test_type in ["DET", "N_DET"]:
        # Convert all SLCO files to Java.
        print("Converting SLCO files for", test_type)
        for root, sub_dirs, files in os.walk("tests"):
            for filename in files:
                if filename.__contains__(".slco") and not root.__contains__("tests\\out"):
                    file_path = os.path.join(root, filename)
                    print("Converting", file_path)
                    try:
                        if test_type == "DET":
                            slco2java.main([file_path, "-t", "10", "-pc"])
                        else:
                            slco2java.main([file_path, "-t", "10", "-pc", "-nds"])
                    except Exception as e:
                        print(e)
        print()

        # Compile all java files.
        print("Compiling Java files for", test_type)
        javac_path = "C:\\Program Files\\Java\\jdk-14.0.1\\bin\\javac"
        for root, sub_dirs, files in os.walk("tests"):
            for filename in files:
                if filename.__contains__(".java") and not root.__contains__("tests\\out"):
                    file_path = os.path.join(root, filename)
                    print("Compiling", file_path)

                    cmd = javac_path + " -d .\\java_out\\" + test_type + "\\" + root + " " + file_path
                    proc = subprocess.Popen(cmd)
                    proc.wait()
        print()

    print("Running Java files and gathering performance data.")
    test_statistics = {
        "DET": dict(),
        "N_DET": dict()
    }
    java_path = "C:\\Program Files\\Java\\jdk-14.0.1\\bin\\java"
    for i in range(0, 2):
        print("Running pass", i)
        for root, sub_dirs, files in os.walk("java_out"):
            for filename in files:
                if filename.__contains__(".class") and not filename.__contains__("$"):
                    file_path = os.path.join(root, filename)
                    class_name = filename.replace(".class", "")
                    test_type = "N_DET" if root.__contains__("N_DET") else "DET"
                    print("Running", file_path)

                    cmd = java_path + " -Xmx4g -Xms4g -cp " + root + " " + class_name
                    proc = subprocess.Popen(cmd, stdout=PIPE, stderr=STDOUT)
                    proc.wait()
                    output = [line.decode("utf-8") for line in proc.stdout.readlines()]
                    if not any(line.__contains__("Exception") for line in output):
                        # Save all the statistics gathered.
                        model_test_statistics = test_statistics[test_type].get(class_name, list())
                        for line in output:
                            print(line, end='')
                        model_test_statistics.append({
                            line.split(";")[0]: line.split(";")[:-1][1:] for line in output
                        })
                        test_statistics[test_type][class_name] = model_test_statistics
                    else:
                        print("Encountered an Exception.")

    with open('objs.pkl', 'wb') as f:
        pickle.dump(test_statistics, f)
else:
    with open('objs.pkl', 'rb') as f:  # Python 3: open(..., 'rb')
        test_statistics = pickle.load(f)

# Process the data.
aggregate_data = dict()
for model, data in test_statistics.items():
    # Find the state machines that are part of the model.
    state_machines = sorted(data[0].keys())

    # Gather aggregate data such as the mean, std, etc.
    aggregate_model_data = {
        "entries": []
    }
    for state_machine in state_machines:
        aggregate_model_data[state_machine] = {
            "entries": []
        }
    for entry in data:
        for state_machine, measurements in entry.items():
            measurement_parse = [
                int(measurements[0]),
                int(measurements[1]),
                float(measurements[2]),
                int(measurements[3]),
            ]
            aggregate_model_data["entries"].append(measurement_parse)
            aggregate_model_data[state_machine]["entries"].append(measurement_parse)

    for state_machine, measurements in aggregate_model_data.items():
        if state_machine != "entries":
            entries = measurements["entries"]
            measurements["mean"] = [mean(v[i] for v in entries) for i in range(0, 4)]
            measurements["max"] = [max(v[i] for v in entries) for i in range(0, 4)]
            measurements["min"] = [min(v[i] for v in entries) for i in range(0, 4)]
            measurements["median"] = [median(v[i] for v in entries) for i in range(0, 4)]
            measurements["stdev"] = [stdev(v[i] for v in entries) for i in range(0, 4)]
            measurements["variance"] = [variance(v[i] for v in entries) for i in range(0, 4)]
            measurements["n"] = [len(entries) for i in range(0, 4)]

    entries = aggregate_model_data["entries"]
    aggregate_model_data["mean"] = [mean(v[i] for v in entries) for i in range(0, 4)]
    aggregate_model_data["max"] = [max(v[i] for v in entries) for i in range(0, 4)]
    aggregate_model_data["min"] = [min(v[i] for v in entries) for i in range(0, 4)]
    aggregate_model_data["median"] = [median(v[i] for v in entries) for i in range(0, 4)]
    aggregate_model_data["stdev"] = [stdev(v[i] for v in entries) for i in range(0, 4)]
    aggregate_model_data["variance"] = [variance(v[i] for v in entries) for i in range(0, 4)]
    aggregate_model_data["n"] = [len(entries) for i in range(0, 4)]

    aggregate_data[model] = aggregate_model_data

    print(model)

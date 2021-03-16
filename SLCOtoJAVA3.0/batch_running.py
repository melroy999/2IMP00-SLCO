import os
import pickle
import subprocess
from subprocess import STDOUT, PIPE

import slco2java


def convert_measurements(measurement):
    return [int(measurement[0]), int(measurement[1]), float(measurement[2]), int(measurement[3])]


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
test_statistics = {"DET": dict(), "N_DET": dict()}
java_path = "C:\\Program Files\\Java\\jdk-14.0.1\\bin\\java"
for i in range(0, 5):
    print("Running pass", i)
    for root, sub_dirs, files in os.walk("java_out"):
        for filename in files:
            if filename.__contains__(".class") and not filename.__contains__("$"):
                file_path = os.path.join(root, filename)
                class_name = filename.replace(".class", "")
                test_type = "N_DET" if root.__contains__("N_DET") else "DET"
                print("Running", file_path)

                cmd = java_path + " -Xmx2g -Xms2g -cp " + root + " " + class_name
                proc = subprocess.Popen(cmd, stdout=PIPE, stderr=STDOUT)
                proc.wait()
                output = [line.decode("utf-8") for line in proc.stdout.readlines()]

                # noinspection PyUnboundLocalVariable
                if not any(line.__contains__("Exception") or line.__contains__("fatal error") for line in output):
                    # Save all the statistics gathered.
                    model_test_statistics = test_statistics[test_type].get(class_name, list())
                    for line in output:
                        print(line, end='')
                    model_test_statistics.append({
                        line.split(";")[0]: convert_measurements(line.split(";")[:-1][1:]) for line in output
                    })
                    test_statistics[test_type][class_name] = model_test_statistics
                else:
                    print("Encountered an Exception.")

with open('objs.pkl', 'wb') as f:
    pickle.dump(test_statistics, f)
import os
import slco2java

rootdir = "tests"
for root, subdirs, files in os.walk(rootdir):
    for filename in files:
        if filename.__contains__(".slco") and not root.__contains__("tests\out"):
            file_path = os.path.join(root, filename)
            print("Processing", file_path)

            try:
                slco2java.main([file_path, "-t", "10", "-pc"])
            except Exception as e:
                print(e)


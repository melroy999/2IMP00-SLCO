//
//  seqcon-analyser.cpp
//  
//
//  Created by Anton Wijs on 11/05/2020.
//

#include <string>
#include <iostream>
#include <fstream>
#include <array>
#include <map>
#include <vector>
using namespace std;

// Memory model
enum MM { TSO, PSO, ARM };
// Access type
enum AccessType { read, condread, write };

// Struct to store info on Memory accesses
struct Access {
	int location;
	AccessType type;
	int instruction;
	int tid;
};

// Struct to store LTS transition
struct Transition {
	int target;
	int label;
};

// Struct to store an LTS state
struct State {
	int id;
	vector<Transition> outgoing;
};

// Struct to store LTS instruction label
struct Instruction {
	int id;
	int oid; // SLCO Object ID
	int tid; // SLCO state machine (thread) ID
	vector<Access> accesses;
};

int main (int argc, char *argv[]) {
	// Create a map from Accesses to integers (indices in vector of Accesses)
	map<Access, int> AccessIndex;

	string modelname = "";
	MM weakmemmodel = TSO;

	if (argc < 2) {
		cout << "Model name missing!" << endl;
		exit(-1);
	}
	for (int i = 1; i < argc; i++) {
		if (strcmp(argv[i], "-m") == 0) {
			i++;
			if (strcmp(argv[i], "TSO") == 0) {
				weakmemmodel = TSO;
			}
			else if (strcmp(argv[i], "PSO") == 0) {
				weakmemmodel = PSO;
			}
			else if (strcmp(argv[i], "ARM") == 0) {
				weakmemmodel = ARM;
			}
			else if (strcmp(argv[i], "POWER") == 0) {
				weakmemmodel = ARM;
			}
			else {
				weakmemmodel = TSO;
			}
		}
		else {
			modelname = string(argv[i]);
			cout << modelname << endl;
		}
	}
	// Reading the input LTS
	string line;
	ifstream ltsfile (modelname);
	if (ltsfile.is_open()) {
		// Skip header
		getline(ltsfile, line);
		while (getline(ltsfile, line)) {
			// Extract info from transition label, and store the transition
			size_t sep1 = line.find_first_of(",");
			string src = line.substr(1,sep1-1);
			cout << src << endl;
			size_t sep2 = line.find_first_of("\"", sep1+2);
			string label = line.substr(sep1+2, sep2-(sep1+2));
			cout << label << endl;
			string tgt = line.substr(sep2+2, line.length()-(sep2+2)-1);
			cout << tgt << endl;
			// Break label further down
			if (label.compare("tau") != 0) {
				label = label.substr(3, label.length()-4);
				cout << label << endl;
				sep1 = label.find_first_of(",");
				string object = label.substr(0, sep1);
				cout << object << endl;
				sep2 = label.find_first_of(",", sep1+1);
				string thread = label.substr(sep1+2, sep2-sep1-2);
				cout << thread << endl;
				sep1 = label.find_first_of(",", sep2+1);
				string statement = label.substr(sep2+2, sep1-sep2-2);
				cout << statement << endl;
				sep2 = label.find_first_of("[", sep1);
				sep1 = label.find_last_of("]");
				cout << sep2 << endl;
				cout << sep1 << endl;
				string accs = label.substr(sep2, sep1-sep2+1);
				while (accs.compare("") != 0) {
					pos1 = accs.find_first_of("'");
				}
			}
		}
		ltsfile.close();
	}
	else {
		cout << "LTS file does not exist!" << endl;
		exit(-1);
	}
}

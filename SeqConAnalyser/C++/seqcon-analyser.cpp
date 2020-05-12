//
//  seqcon-analyser.cpp
//  
//
//  Created by Anton Wijs on 11/05/2020.
//

#include <string>
#include <iostream>
#include <fstream>
#include <map>
#include <vector>
using namespace std;

// Memory model
enum MM { TSO, PSO, ARM };
// Access type
enum AccessType { read, condread, write };

// Template class to maintain a dictionary of objects
// of type A_Type, each mapped to a unique ID.
template <class A_Type> class IndexedDict {
	private:
		map<A_Type, int> m;
		vector<A_Type> storage;
		int counter;
	public:
		IndexedDict() {
			counter = 0;
		}

		// Store item, if not yet done, and return index in storage
		int insert(A_Type item) {
			auto it = m.find(item);
			if (it != m.end()) {
				return it->second;
			}
			else {
				auto it = storage.begin();
				storage.insert(it, item);
				m.insert(item, counter++);
				return counter;
			}
		}

		// Get item at given index in storage
		A_Type get(int index) {
			return storage[index];
		}
};

// Struct to store info on Memory accesses
struct Access {
	int location; // Memory location
	bool local; // Is the variable local or not?
	AccessType type; // Type of access
	int instruction; // Instruction of which the access is part
	int tid; // Thread executing the access
};

// Struct to store LTS transition
struct Transition {
	int target; // Target state
	int label; // Instruction associated with the transition
};

// Struct to store an LTS state
struct State {
	int id; // State id
	vector<Transition> outgoing; // List of outgoing transitions
};

// Struct to store LTS instruction label
struct Instruction {
	int id; // Instruction ID
	int tid; // SLCO state machine (thread) ID
	vector<Access> accesses; // List of accesses performed by the instruction
};

int main (int argc, char *argv[]) {
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
	// PR relation
	map<Access, vector<Access>> pr;
	// CMP relation
	map<Access, vector<Access>> cmp;
	// Various IndexedDicts to keep track of information extracted from the LTS
	IndexedDict<string> instruction_ids;
	IndexedDict<string> thread_ids;
	IndexedDict<string> location_ids;
	IndexedDict<Transition> transitions;
	IndexedDict<Access> accesses;

	// Reading the input LTS
	string line;
	ifstream ltsfile (modelname);
	if (ltsfile.is_open()) {
		// Header: extract number of states
		getline(ltsfile, line);
		size_t sep1 = line.find_last_of(",");
		int nr_of_states = stoi(line.substr(sep1+1, line.find_last_of(")")-(sep1+1)));
		// Create vector for states
		vector<State> lts_states(nr_of_states);

		while (getline(ltsfile, line)) {
			// Extract info from transition label, and store the transition
			sep1 = line.find_first_of(",");
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
				sep2 = label.find_first_of(",", sep1+1);
				string thread = label.substr(sep1+2, sep2-sep1-2);
				cout << thread << endl;
				sep1 = label.find_first_of(",", sep2+1);
				string statement = label.substr(sep2+2, sep1-sep2-2);
				cout << statement << endl;

				// Retrieve thread and instruction IDs, and retrieve instruction index
				int iid = instruction_ids.insert(statement);
				int tid = thread_ids.insert(thread);
				Instruction instr;
				instr.id = iid;
				instr.tid = tid;

				sep2 = label.find_first_of("[", sep1);
				sep1 = label.find_last_of("]");
				cout << sep2 << endl;
				cout << sep1 << endl;
				string accs = label.substr(sep2, sep1-sep2+1);

				while (accs.compare("") != 0) {
					sep1 = accs.find_first_of("'");
					if (sep1 == string::npos) {
						break;
					}
					// Find the first closing ']', indicating the end of the (next) list of read accesses
					sep2 = accs.find_first_of("]");
					string reads = accs.substr(sep1+3, sep2-(sep1+3));
					while (reads.compare("") != 0) {
						sep1 = reads.find_first_of(",]");
						string read = reads.substr(0, sep1);
						cout << read << endl;
						int start = sep1+1+(reads[sep1] == ',' ? 1 : 0);
						reads = reads.substr(start, reads.length()-start);
					}
					// Find the next "[" and "]", the list of write accesses
					sep1 = accs.find_first_of("[", sep2);
					sep2 = accs.find_first_of("]", sep1);
					string writes = accs.substr(sep1+1, sep2-(sep1+1));
					cout << writes << endl;
					accs = accs.substr(sep2);
					cout << accs << endl;
				}
				// Store the extracted information

			}
		}
		ltsfile.close();
	}
	else {
		cout << "LTS file does not exist!" << endl;
		exit(-1);
	}
}

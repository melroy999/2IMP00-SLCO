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
#include <algorithm>
using namespace std;

// Memory model
enum MM { TSO, PSO, ARM };
// Access type
enum AccessType { READ, CONDREAD, WRITE };

// Template class to maintain a map of objects
// of type A_Type, each mapped to a unique ID.
template <class A_Type> class IndexedMap {
	private:
		map<A_Type, int> m;
		int counter;
	public:
		IndexedMap() {
			counter = 0;
		}

		// Store item, if not yet done, and return index in storage
		int insert(A_Type item) {
			auto it = m.find(item);
			if (it != m.end()) {
				return it->second;
			}
			else {
				m.insert(pair<A_Type, int>(item, counter));
				return counter++;
			}
		}

		// Find the given item, and return its index. If not present, return -1
		int find(A_Type item) {
			auto it = m.find(item);
			if (it != m.end()) {
				return it->second;
			}
			else {
				return -1;
			}
		}
};

// Template class for a searchable vector of elements of type A_Type.
// A map is used for the searching of elements. 
template <class A_Type> class SearchableVector {
	private:
		map<A_Type, int> m;
		vector<A_Type> storage;
		int counter;
	public:
		SearchableVector() {
			counter = 0;
		}

		// Store item, if not yet done, and return index in storage
		int insert(A_Type item) {
			auto it = m.find(item);
			if (it == m.end()) {
				m.insert(pair<A_Type, int>(item, counter));
				storage.insert(storage.end(), item);
				return counter++;
			}
			else {
				return it->second;
			}
		}

		// Find the given item, and return its index. If not present, return -1
		int find(A_Type item) {
			auto it = m.find(item);
			if (it != m.end()) {
				return it->second;
			}
			else {
				return -1;
			}
		}

		// Get the element at given index
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
	bool cond_only; // Is the access part of checking a condition only, or of executing a complete instruction?
};

bool operator<(const Access& a1, const Access& a2) {
     return (a1.location<a2.location || (a1.location==a1.location && a1.local<a2.local)
     	|| (a1.location==a1.location && a1.local==a2.local && a1.type < a2.type)
     	|| (a1.location==a1.location && a1.local==a2.local && a1.type==a2.type && a1.instruction < a2.instruction)
     	|| (a1.location==a1.location && a1.local==a2.local && a1.type==a2.type && a1.instruction==a2.instruction && a1.tid < a2.tid)
        || (a1.location==a1.location && a1.local==a2.local && a1.type==a2.type && a1.instruction==a2.instruction && a1.tid==a2.tid && a1.cond_only < a2.cond_only) );
}

// Struct to store LTS instruction label
struct Instruction {
	int tid; // SLCO state machine (thread) ID
	vector<int> accesses; // List of accesses performed by the instruction
};

// Struct to store an LTS state
struct State {
	int outgoing_begin = -1; // Start of list of outgoing transitions
	int outgoing_end = -1; // End of list of outgoing transitions
};

// Struct to store LTS transition
struct Transition {
	int target; // Target state
	map<string, Instruction>::iterator instruction; // Instruction associated with the transition
};

int main (int argc, char *argv[]) {
	string modelname = "";
	MM weakmemmodel = TSO;
	bool check_atomicity = false;

	if (argc < 2) {
		cout << "Model name missing!" << endl;
		exit(-1);
	}
	for (int i = 1; i < argc; i++) {
		if (strcmp(argv[i], "-w") == 0) {
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
		else if (strcmp(argv[i], "-a") == 0) {
			check_atomicity = true;
		}
		else if (strcmp(argv[i], "-h") == 0) {
			cout << "Usage: seqcon-analyser [-wsa] model" << endl;
			cout << "" << endl;
			cout << "Check for sequentially inconsistent behaviour in the given .aut file containing the state space of an SLCO model, unless '-s' is used." << endl;
			cout << " -w                                  weak memory model to consider (SC,TSO,PSO,ARM)  (default: TSO)" << endl;
			cout << " -s                                  apply only static analysis (ignore state space) (default: no)" << endl;
			cout << "                                       -> this option requires a .instr file listing the instructions of the SLCO model" << endl;
			cout << " -a                                  apply atomicity checking in combination with SC checking (default: no)" << endl;
		}
		else {
			modelname = string(argv[i]);
			cout << modelname << endl;
		}
	}

	// Accesses
	SearchableVector<Access> accesses;

	// PR relation
	map<int, vector<int>> PR;
	// CMP relation
	map<int, vector<int>> CMP;
	
	// Various IndexedMaps to keep track of information extracted from the LTS
	IndexedMap<string> instruction_positions;
	map<string, Instruction> instructions;
	IndexedMap<string> thread_ids;
	IndexedMap<string> location_ids;

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
		size_t sep2 = line.find_first_of(",");
		int nr_of_trans = stoi(line.substr(sep2+1, sep1-(sep2+1)));
		// Create vector for transitions
		vector<Transition> lts_transitions(nr_of_trans);

		int current_state_index = -1;
		int current_trans_index = 0;
		// Instruction instance to be used to create new instructions
		Instruction instr;
		// Access instance to be used to create new accesses
		Access acc;
		int prev_src = -1;
		bool first_trans;
		while (getline(ltsfile, line)) {
			// Extract info from transition label, and store the transition
			sep1 = line.find_first_of(",");
			int src = stoi(line.substr(1,sep1-1));
			if (src != prev_src) {
				if (prev_src != -1) {
					lts_states[prev_src].outgoing_end = current_trans_index;
				}
				first_trans = true;
				prev_src = src;
				current_state_index++;
			}
			else {
				first_trans = false;
			}
			sep2 = line.find_first_of("\"", sep1+2);
			string translabel = line.substr(sep1+2, sep2-(sep1+2));
			int tgt = stoi(line.substr(sep2+2, line.length()-(sep2+2)-1));
			// List of previous and current accesses, used to build intra-instruction PR-relation
			vector<int> prev_accesses, curr_accesses;

			// Check if instruction is already stored. If not, create it
			if (instructions.find(translabel) == instructions.end()) {
				if (translabel.compare("tau") != 0) {
					//cout << translabel << endl;
					// Break label further down
					string label = translabel.substr(3, translabel.length()-4);
					// cout << label << endl;
					sep1 = label.find_first_of(",");
					sep2 = label.find_first_of(",", sep1+1);
					string thread = label.substr(sep1+2, sep2-sep1-2);
					int tid = thread_ids.insert(thread);
					sep1 = label.find_first_of(",", sep2+1);
					string statement = label.substr(sep2+2, sep1-sep2-2);
					int iid = instruction_positions.insert(statement);

					// Set the instruction info
					instr.tid = tid;
					instr.accesses.clear();

					sep2 = label.find_first_of("[", sep1);
					sep1 = label.find_last_of("]");
					// cout << sep2 << endl;
					// cout << sep1 << endl;
					string accs = label.substr(sep2, sep1-sep2+1);
					// cout << "Accs:" << endl;
					// cout << accs << endl;

					// List of previous and current accesses, used to build intra-instruction PR-relation
					prev_accesses.clear();
					curr_accesses.clear();

					while (accs.compare("") != 0) {
						sep1 = accs.find_first_of("'");
						if (sep1 == string::npos) {
							break;
						}
						// Find the first closing ']', indicating the end of the (next) list of read accesses
						sep2 = accs.find_first_of("]", sep1);
						string reads = accs.substr(sep1+3, sep2-(sep1+3));
						// Find the next "[" and "]", the corresponding list of write accesses
						sep1 = accs.find_first_of("[", sep2);
						sep2 = accs.find_first_of("]", sep1);
						string writes = accs.substr(sep1+1, sep2-(sep1+1));
						accs = accs.substr(sep2);

						while (reads.compare("") != 0) {
							// cout << "Reads:" << endl;
							// cout << reads << endl;
							sep1 = reads.find_first_of(",");
							if (sep1 == string::npos) {
								sep1 = reads.length();
							}
							string read = reads.substr(0, sep1);

							// Create and store read access
							int loc = location_ids.insert(read);
							acc.location = loc;
							// cout << loc << endl;
							// Is the variable thread-local? (encoded in name by the fact that ' occurs more than once)
							acc.local = count(read.begin(), read.end(), '\'') > 1;
							// cout << acc.local << endl;
							acc.type = (writes.compare("") == 0 ? CONDREAD : READ);
							// cout << acc.type << endl;
							acc.instruction = iid;
							// cout << acc.instruction << endl;
							acc.tid = tid;
							// cout << tid << endl;
							acc.cond_only = (src == tgt && accs.find_first_of("'") == string::npos && writes.compare("") == 0);
							// cout << acc.cond_only << endl;
							int aid = accesses.insert(acc);
							//cout << "read " << aid << " : " << read << endl;
							instr.accesses.insert(instr.accesses.end(), aid);
							curr_accesses.insert(curr_accesses.end(), aid);

							// cout << read << endl;
							int start = sep1+(sep1 < reads.length() ? 2 : 0);
							reads = reads.substr(start, reads.length()-start);
							// cout << "here" << endl;
						}
						if (!curr_accesses.empty()) {
							// If needed, update PR
							if (!prev_accesses.empty()) {
								for (auto a : prev_accesses) {
									PR.insert(pair<int, vector<int>>(a, curr_accesses));
								}
							}
							// Swap lists of accesses
							prev_accesses = curr_accesses;
							curr_accesses.clear();
						}

						while (writes.compare("") != 0) {
							// cout << "Writes:" << endl;
							// cout << writes << endl;
							sep1 = writes.find_first_of(",");
							if (sep1 == string::npos) {
								sep1 = writes.length();
							}
							string write = writes.substr(0, sep1);

							// Create and store write access
							int loc = location_ids.insert(write);
							acc.location = loc;
							// cout << loc << endl;
							// Is the variable thread-local? (encoded in name by the fact that ' occurs more than once)
							acc.local = count(write.begin(), write.end(), '\'') > 1;
							// cout << acc.local << endl;
							acc.type = WRITE;
							// cout << acc.type << endl;
							acc.instruction = iid;
							// cout << acc.instruction << endl;
							acc.tid = tid;
							// cout << tid << endl;
							acc.cond_only = false;
							// cout << acc.cond_only << endl;
							int aid = accesses.insert(acc);
							//cout << "write " << aid << " : " << write << endl;
							instr.accesses.insert(instr.accesses.end(), aid);
							curr_accesses.insert(curr_accesses.end(), aid);

							// cout << write << endl;
							int start = sep1+(sep1 < writes.length() ? 2 : 0);
							writes = writes.substr(start, writes.length()-start);
							// cout << "here" << endl;
						}
						// cout << accs << endl;

						if (!curr_accesses.empty()) {
							// If needed, update PR
							if (!prev_accesses.empty()) {
								for (auto a : prev_accesses) {
									PR.insert(pair<int, vector<int>>(a, curr_accesses));
								}
							}
							// Swap lists of accesses
							prev_accesses = curr_accesses;
							curr_accesses.clear();
						}
					}
				}
				else {
					// Store a dummy tau instruction
					instr.tid = -1;
					instr.accesses.clear();
				}
				// Store the instruction
				auto it = instructions.insert(pair<string, Instruction>(translabel, instr));
			}
			// Get the instruction
			auto it = instructions.find(translabel);
			// Store the transition
			lts_transitions[current_trans_index].target = tgt;
			lts_transitions[current_trans_index].instruction = it;
			// Store the source state info
			if (first_trans) {
				lts_states[current_state_index].outgoing_begin = current_trans_index;
			}
			current_trans_index++;
		}
		// Store outgoing transitions end for final state
		lts_states[current_state_index].outgoing_end = current_trans_index;
		// for (auto i = instructions.begin(); i != instructions.end(); ++i) {
		// 	cout << (*i).second.label << endl;
		// 	cout << (*i).second.tid << endl;
		// }
		for (auto i : PR) {
			for (auto j : i.second) {
				cout << "(" << i.first << ", " << j << ")" << endl;
			}
		}
		ltsfile.close();
	}
	else {
		cout << "LTS file does not exist!" << endl;
		exit(-1);
	}
}

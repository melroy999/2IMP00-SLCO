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
#include <set>
#include <algorithm>

using namespace std;

// Memory model
enum MM { TSO, PSO, ARM };
// Access type
enum AccessType { READ, WRITE };

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

		typedef typename vector<A_Type>::iterator VAiterator;

		VAiterator begin() {
			return storage.begin();
		}

		VAiterator end() {
			return storage.end();
		}
};

// Class to maintain a relation between integers.
class Relation {
	private:
		map<int, set<int>> r;
	public:
		void insert(int i, vector<int> J) {
			auto it = r.find(i);
			if (it == r.end()) {
				r.insert(pair<int, set<int>>(i, set<int>(J.begin(), J.end())));
			}
			else {
				copy(J.begin(), J.end(), inserter(it->second, it->second.end()));
			}
		}

		void insert(int i, int j) {
			auto it = r.find(i);
			if (it == r.end()) {
				r.insert(pair<int, set<int>>(i, { j }));
			}
			else {
				it->second.insert(j);
			}
		}

		bool contains(int i) {
			auto it = r.find(i);
			return (it != r.end());
		}

		// Precondition: an entry exists for i in r
		map<int, set<int>>::iterator get(int i) {
			return r.find(i);
		}

		map<int, set<int>>::iterator begin() {
			return r.begin();
		}
		map<int, set<int>>::iterator end() {
			return r.end();
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

// < operator for Accesses, to be able to store them in a map
bool operator<(const Access& a1, const Access& a2) {
     return (a1.location<a2.location || (a1.location==a2.location && a1.local<a2.local)
     	|| (a1.location==a2.location && a1.local==a2.local && a1.type < a2.type)
     	|| (a1.location==a2.location && a1.local==a2.local && a1.type==a2.type && a1.instruction < a2.instruction)
     	|| (a1.location==a2.location && a1.local==a2.local && a1.type==a2.type && a1.instruction==a2.instruction && a1.tid < a2.tid));
}

// Struct to store LTS instruction label
struct Instruction {
	int pos; // Instruction position in the input model
	int tid; // SLCO state machine (thread) ID
	bool is_guarded; // Does the instruction have a condition?
	vector<int> shared_accesses; // List of shared accesses performed by the instruction
	vector<int> bottom_accs; // List of PR-smallest accesses
	vector<int> top_accs; // List of PR-largest accesses
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
			cout << " -w                                  weak memory model to consider (TSO,PSO,ARM)  (default: TSO)" << endl;
			cout << " -s                                  apply only static analysis (ignore state space) (default: no)" << endl;
			cout << "                                       -> this option requires a .instr file listing the instructions of the SLCO model" << endl;
			cout << " -a                                  apply atomicity checking in combination with SC checking (default: no)" << endl;
		}
		else {
			modelname = string(argv[i]);
		}
	}

	// Accesses
	SearchableVector<Access> accesses;

	// PR relation
	Relation PR;
	// Transitive closure of PR
	Relation PRplus;
	// Dependency relations (DP and 'direct' (non-transitive) version DPdirect)
	Relation DP;
	Relation DPdirect;
	// RF relation for thread-local variables; needed to close DP
	Relation RFlocal;
	// CMP relation
	Relation CMP;
	
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
			vector<int> prev_accesses, curr_accesses_bottom, curr_accesses_top;

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
					instr.pos = iid;
					instr.tid = tid;
					instr.is_guarded = false;
					instr.shared_accesses.clear();
					instr.bottom_accs.clear();
					instr.top_accs.clear();

					sep2 = label.find_first_of("[", sep1);
					sep1 = label.find_last_of("]");
					// cout << sep2 << endl;
					// cout << sep1 << endl;
					string accs = label.substr(sep2, sep1-sep2+1);
					// cout << "Accs:" << endl;
					// cout << accs << endl;

					// List of previous and current accesses, used to build intra-instruction PR-relation
					prev_accesses.clear();
					curr_accesses_bottom.clear();
					curr_accesses_top.clear();

					bool first = true;

					while (accs.compare("") != 0) {
						sep1 = accs.find_first_of("'");
						if (sep1 == string::npos) {
							break;
						}
						// Find the matching closing ']' of the reads of the next access pattern,
						// indicating the end of the (next) list of read accesses
						int bracket_counter = 0;
						for (sep2 = sep1+2; sep2 < accs.length(); sep2++) {
							if (accs[sep2] == ']') {
								if (bracket_counter == 1) {
									break;
								}
								else {
									bracket_counter--;
								}
							}
							else if (accs[sep2] == '[') {
								bracket_counter++;
							}
						}
						//cout << "label: " << accs << endl;
						string reads = accs.substr(sep1+2, sep2-(sep1+1));
						//cout << "reads: " << reads << endl;
						// Find the next "[" and "]", the corresponding list of write accesses
						sep1 = accs.find_first_of("[", sep2);
						sep2 = accs.find_first_of("]", sep1);
						string writes = accs.substr(sep1, sep2+1-sep1);
						accs = accs.substr(sep2);
						//cout << "writes: " << writes << endl;

						bool reads_stored = false;

						while (true) {
							// cout << "Reads:" << endl;
							// cout << reads << endl;
							sep2 = reads.find_first_of("'");
							if (sep2 == string::npos) {
								break;
							}
							// Record the read access
							sep1 = reads.find_first_of(",", sep2);
							if (sep1 == string::npos) {
								sep1 = reads.length()-1;
							}
							if (reads[sep2-1] == 'c') {
								sep1--;
							}
							string read = reads.substr(sep2+2, sep1-(sep2+2));
							//cout << read << endl;

							// The instruction is guarded if there are no writes at this point
							if (writes.compare("[]") == 0) {
								instr.is_guarded = true;
							}

							// Create and store read access
							int loc = location_ids.insert(read);
							acc.location = loc;
							// cout << loc << endl;
							// Is the variable thread-local? (encoded in name by the fact that ' occurs more than once)
							acc.local = count(read.begin(), read.end(), '\'') > 1;
							// cout << acc.local << endl;
							acc.type = READ;
							// cout << acc.type << endl;
							acc.instruction = iid;
							// cout << acc.instruction << endl;
							acc.tid = tid;
							// cout << tid << endl;
							int aid = accesses.insert(acc);
							cout << "read " << aid << " : " << read << ": " << label << endl;
							if (!acc.local) {
								instr.shared_accesses.insert(instr.shared_accesses.end(), aid);
							}
							reads_stored = true;

							if (reads[sep2-1] != 'p') {
								curr_accesses_bottom.insert(curr_accesses_bottom.end(), aid);
							}
							else {
								curr_accesses_top.insert(curr_accesses_bottom.end(), aid);
							}

							if (reads[sep2-1] == 'p') {
								// we have a tuple with a read and a list of address dependencies of that read
								// record the dependencies
								size_t sep3 = sep1+3;
								while (true) {
									size_t sep4 = reads.find_first_of(",]", sep3);
									string depread = reads.substr(sep3, sep4-sep3);
									//cout << "depread: " << depread << endl;
									// Store this read access
									loc = location_ids.insert(depread);
									acc.location = loc;
									acc.local = count(depread.begin(), depread.end(), '\'') > 1;
									int depaid = accesses.insert(acc);
									cout << "read " << depaid << " : " << depread << ": " << label << endl;

									// Store dependencies
									DPdirect.insert(aid, depaid);
									PR.insert(depaid, aid);

									sep3 = sep4+2;
									if (reads[sep4] == ']') {
										break;
									}
								}
								reads = reads.substr(sep3, reads.length()-sep3);
								//cout << "reads: " << reads << endl;
							}
							else {
								reads = reads.substr(sep1, reads.length()-sep1);
							}
						}
						if (!curr_accesses_bottom.empty()) {
							// If needed, update PR
							if (!prev_accesses.empty()) {
								for (auto a : prev_accesses) {
									PR.insert(a, curr_accesses_bottom);
								}
							}
							// Store PR-smallest accesses
							if (first) {
								first = false;
								instr.bottom_accs.insert(instr.bottom_accs.end(), curr_accesses_bottom.begin(), curr_accesses_bottom.end());
							}
							// Swap lists of accesses
							if (!curr_accesses_top.empty()) {
								prev_accesses = curr_accesses_top;
								curr_accesses_top.clear();
							}
							else {
								prev_accesses = curr_accesses_bottom;
							}
							curr_accesses_bottom.clear();
						}

						while (true) {
							// cout << "Writes:" << endl;
							// cout << writes << endl;
							sep1 = writes.find_first_of("'");
							if (sep1 == string::npos) {
								break;
							}
							sep2 = writes.find_first_of(",");
							if (sep2 == string::npos) {
								sep2 = writes.length()-1;
							}
							sep2--;
							string write = writes.substr(sep1+2, sep2-(sep1+2));

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
							int aid = accesses.insert(acc);
							//cout << "write " << aid << " : " << write << endl;
							if (!acc.local) {
								instr.shared_accesses.insert(instr.shared_accesses.end(), aid);
							}
							curr_accesses_bottom.insert(curr_accesses_bottom.end(), aid);

							//cout << write << endl;
							writes = writes.substr(sep2, writes.length()-sep2);
							// cout << "here" << endl;
						}
						// cout << accs << endl;

						if (!curr_accesses_bottom.empty()) {
							// If needed, update PR
							if (!prev_accesses.empty()) {
								for (auto a : prev_accesses) {
									PR.insert(a, curr_accesses_bottom);
								}
								// Writes depend on directly preceding reads
								if (reads_stored) {
									for (auto a : curr_accesses_bottom) {
										DPdirect.insert(a, prev_accesses);
									}
								}
							}
							// Store PR-smallest accesses
							if (first) {
								first = false;
								instr.bottom_accs.insert(instr.bottom_accs.end(), curr_accesses_bottom.begin(), curr_accesses_bottom.end());
							}
							// Swap lists of accesses
							prev_accesses = curr_accesses_bottom;
							curr_accesses_bottom.clear();
						}
					}
					// Store PR-largest accesses
					instr.top_accs.insert(instr.top_accs.end(), prev_accesses.begin(), prev_accesses.end());
				}
				else {
					// Store a dummy tau instruction
					instr.tid = -1;
					instr.shared_accesses.clear();
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
		// for (auto i : PR) {
		// 	for (auto j : i.second) {
		// 		cout << "(" << i.first << ", " << j << ")" << endl;
		// 	}
		// }
		ltsfile.close();

		// Set of (instruction position, thread id) pairs of outgoing transitions of a state
		set<pair<int, int>> out;
		// Compute inter-instruction PR
		for (auto s : lts_states) {
			out.clear();
			// Collect info on outgoing transitions
			for (int i = s.outgoing_begin; i < s.outgoing_end; i++) {
				auto instr = (*(lts_transitions[i].instruction)).second;
				out.insert(pair<int, int>(instr.pos, instr.tid));
			}
			// Check successors
			for (int i = s.outgoing_begin; i < s.outgoing_end; i++) {
				int tgt = lts_transitions[i].target;
				auto instr = (*(lts_transitions[i].instruction)).second;
				int pos = instr.pos;
				int tid = instr.tid;
				for (int j = lts_states[tgt].outgoing_begin; j < lts_states[tgt].outgoing_end; j++) {
					auto tgt_instr = (*(lts_transitions[j].instruction)).second;
					int tgt_pos = tgt_instr.pos;
					int tgt_tid = tgt_instr.tid;
					if (tgt_tid == tid) {
						if (out.find(pair<int, int>(tgt_pos, tgt_tid)) == out.end()) {
							// PR-relate top elements of instr with bottom elements of tgt_instr
							for (auto ta : instr.top_accs) {
								PR.insert(ta, tgt_instr.bottom_accs);
							}
						}
					}
				}
			}
		}

		// Compute the RF relation for thread-local variables
		set<int> open;
		set<int> closed;
		for (auto i : PR) {
			Access a = accesses.get(i.first);
			if (a.local && a.type == WRITE) {
				open.clear();
				closed.clear();
				closed.insert(i.first);
				// Search for reachable reads from the same location
				open.insert(i.second.begin(), i.second.end());
				while (!open.empty()) {
					int j = *(open.begin());
					open.erase(j);
					closed.insert(j);
					Access b = accesses.get(j);
					if (a.location == b.location) {
						if (b.type == READ) {
							RFlocal.insert(j, i.first);
						}
					}
					else {
						if (PR.contains(j)) {
							auto it = PR.get(j);
							for (auto k : it->second) {
								if (closed.find(k) == closed.end()) {
									open.insert(k);
								}
							}
						}
					}
				}
			}
		}
		// Close DPdirect over local variables, using RFlocal. This results in DP
		for (auto i : DPdirect) {
			Access a = accesses.get(i.first);
			if (!a.local) {
				open.clear();
				closed.clear();
				closed.insert(i.first);
				open.insert(i.second.begin(), i.second.end());
				while (!open.empty()) {
					int j = *(open.begin());
					open.erase(j);
					closed.insert(j);
					Access b = accesses.get(j);
					if (!b.local) {
						DP.insert(i.first, j);
					}
					else {
						auto it = RFlocal.get(j);
						for (auto k : it->second) {
							if (DPdirect.contains(k)) {
								auto it2 = DPdirect.get(k);
								for (auto l : it2->second) {
									if (closed.find(l) == closed.end()) {
										open.insert(l);
									}
								}
							}
						}
					}
				}
			}
		}

		cout << "locality info:" << endl;
		for (auto a : accesses) {
			cout << accesses.find(a) << ": " << a.local << endl;
		}
		cout << "PR:" << endl;
		for (auto i : PR) {
			for (auto j : i.second) {
				cout << "(" << i.first << ", " << j << ")" << endl;
			}
		}
		cout << "RFlocal:" << endl;
		for (auto i : RFlocal) {
			for (auto j : i.second) {
				cout << "(" << i.first << ", " << j << ")" << endl;
			}
		}
		cout << "DPdirect:" << endl;
		for (auto i : DPdirect) {
			for (auto j : i.second) {
				cout << "(" << i.first << ", " << j << ")" << endl;
			}
		}
		cout << "DP:" << endl;
		for (auto i : DP) {
			for (auto j : i.second) {
				cout << "(" << i.first << ", " << j << ")" << endl;
			}
		}
	}
	else {
		cout << "LTS file does not exist!" << endl;
		exit(-1);
	}
}

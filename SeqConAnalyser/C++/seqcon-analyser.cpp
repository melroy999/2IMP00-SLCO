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
		A_Type& get(int index) {
			return storage.at(index);
		}

		typedef typename vector<A_Type>::iterator VAiterator;

		VAiterator begin() {
			return storage.begin();
		}

		VAiterator end() {
			return storage.end();
		}

		int size() {
			return storage.size();
		}
};

// Class to maintain a relation between integers.
class Relation {
	protected:
		map<int, set<int>> r;
	public:
		void copy(Relation R) {
			r.clear();
			r.insert(R.begin(), R.end());
		}

		virtual void insert(int i, vector<int> J) {
			auto it = r.find(i);
			if (it == r.end()) {
				r.insert(pair<int, set<int>>(i, set<int>(J.begin(), J.end())));
			}
			else {
				::copy(J.begin(), J.end(), inserter(it->second, it->second.end()));
			}
		}

		virtual void insert(int i, int j) {
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

		bool are_related(int i, int j) {
			if (!contains(i)) {
				return false;
			}
			else {
				auto it = get(i);
				return it->second.find(j) != it->second.end();
			}
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

// Class to maintain a bidirectional relation between integers.
// Checking in the opposite direction of the relation can be done efficiently.
class BiRelation : public Relation {
	protected:
		map<int, set<int>> r_rev;
	public:
		typedef int value_type;

		void copy(BiRelation R) {
			r.clear();
			r_rev.clear();
			r.insert(R.begin(), R.end());
			r_rev.insert(R.rev_begin(), R.rev_end());
		}

		void insert(int i, vector<int> J) override {
			auto it = r.find(i);
			if (it == r.end()) {
				r.insert(pair<int, set<int>>(i, set<int>(J.begin(), J.end())));
			}
			else {
				::copy(J.begin(), J.end(), inserter(it->second, it->second.end()));
			}
			for (auto j : J) {
				it = r_rev.find(j);
				if (it == r_rev.end()) {
					r_rev.insert(pair<int, set<int>>(j, { i }));
				}
				else {
					it->second.insert(i);
				}
			}
		}

		void insert(int i, int j) override {
			auto it = r.find(i);
			if (it == r.end()) {
				r.insert(pair<int, set<int>>(i, { j }));
			}
			else {
				it->second.insert(j);
			}
			it = r_rev.find(j);
			if (it == r_rev.end()) {
				r_rev.insert(pair<int, set<int>>(j, { i }));
			}
			else {
				it->second.insert(i);
			}
		}

		// Insert into the relation element i, with predecessors pred and successors succ
		void insert(int i, vector<int> pred, vector<int> succ) {
			insert(i, succ);
			for (auto ai : pred) {
				insert(ai, i);
			}
		}

		// Remove the relation between i and j
		void remove(int i, int j) {
			if (contains(i)) {
				auto it = get(i);
				it->second.erase(j);
				it = get_rev(j);
				it->second.erase(i);
			}
		}

		// Update the relation for element i
		void update(int i, vector<int> pred, vector<int> succ) {
			if (contains(i)) {
				auto it = get(i);
				for (auto ai : it->second) {
					(get_rev(ai))->second.erase(i);
					if ((get_rev(ai))->second.empty()) {
						r_rev.erase(ai);
					}
				}
				if (succ.empty()) {
					r.erase(i);
				}
				else {
					it->second.clear();
				}
			}
			insert(i, pred, succ);
		}

		bool contains_rev(int i) {
			auto it = r_rev.find(i);
			return (it != r_rev.end());
		}

		// Precondition: an entry exists for i in r_rev
		map<int, set<int>>::iterator get_rev(int i) {
			return r_rev.find(i);
		}

		map<int, set<int>>::iterator rev_begin() {
			return r_rev.begin();
		}

		map<int, set<int>>::iterator rev_end() {
			return r_rev.end();
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
	set<int> accesses; // Set of accesses performed by the instruction
	vector<int> bottom_accs; // List of PR-smallest accesses
	vector<int> cond_reads; // List of reads to check a condition, in addition to the ones in bottom_accs
							// (the reads in cond_reads are address dependent on some in bottom_accs)
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
	map<int, Instruction>::iterator instruction; // Instruction associated with the transition
};

// Function to check whether two accesses can be reordered
bool can_reorder(int ai, int bi, SearchableVector<Access> accesses, MM mmodel, Relation DP, Relation CTRL) {
	Access& a = accesses.get(ai);
	Access& b = accesses.get(bi);
	if (a.type == WRITE) {
		if (b.type == WRITE) {
			if (a.location == b.location) {
				return false;
			}
			else {
				return !(mmodel == TSO);
			}
		}
		else {
			return true;
		}
	}
	else {
		if (b.type == WRITE) {
			if (mmodel != ARM) {
				return false;
			}
			else {
				if (DP.are_related(bi, ai)) {
					return false;
				}
				else return !CTRL.are_related(bi, ai);
			}
		}
		else {
			if (mmodel != ARM) {
				return false;
			}
			else {
				return !(a.location == b.location || DP.are_related(bi, ai));
			}
		}
	}
}

// Function to PPR-reorder a given access ai, under the given relations, into the given instruction.
// Precondition: if ai stems from another instruction, then it is not yet reordered into instruction instr_id.
// Postcondition: ai is properly placed in the PPR-relation.
bool reorder(int ai, int instr_id, map<int, Instruction> instructions, SearchableVector<Access> accesses, MM mmodel,
				vector<BiRelation>& PPR, BiRelation PR, Relation DP, Relation CTRL, bool from_outside_instr) {
	// Get the PPR-predecessors of ai.
	bool moved_into = false;
	auto instr = (instructions.find(instr_id))->second;
	if ((!from_outside_instr && PR.contains_rev(ai)) || (from_outside_instr && !(instr.top_accs.empty()))) {
		set<int> set1, set2;
		set<int>& open = set1;
		set<int>& tmp = set1;
		set<int>& next = set2;

		if (!from_outside_instr) {
			auto it_pred = PR.get_rev(ai);
			for (auto bi : it_pred->second) {
				if (instr.accesses.find(bi) != instr.accesses.end()) {
					open.insert(bi);
				}
			}
		}
		else {
			for (int bi : instr.top_accs) {
				open.insert(bi);
			}
		}
		while (!open.empty()) {
			for (int bi : open) {
				if (can_reorder(bi, ai, accesses, mmodel, DP, CTRL)) {
					if (!from_outside_instr) {
						if (PR.contains_rev(bi)) {
							auto it = PR.get_rev(bi);
							for (auto ci : it->second) {
								if (instr.accesses.find(ci) != instr.accesses.end()) {
									next.insert(ci);
								}
							}
						}
					}
					else {
						if (PPR[instr_id].contains_rev(bi)) {
							auto it = PPR[instr_id].get_rev(bi);
							next.insert(it->second.begin(), it->second.end());
						}
						if (!moved_into) {
							instr.accesses.insert(ai);
							moved_into = true;
						}
					}
				}
				else {
					// ai cannot be reordered before bi, but maybe it can be, together with bi, before bi's PR-predecessors (those that are not PPR-predecessors of bi,
					// since we require that bi can also be reordered before them).
					cout << "here " << instr_id << " " << bi << " " << ai << endl;
					PPR[instr_id].insert(bi, ai);
					if (!from_outside_instr) {
						if (PR.contains_rev(bi)) {
							map<int, set<int>>::iterator it_bi_pr_pred = PR.get_rev(bi);
							map<int, set<int>>::iterator it_bi_ppr_pred;
							bool has_PPR_preds = false;
							if (PPR[instr_id].contains_rev(bi)) {
								it_bi_ppr_pred = PPR[instr_id].get_rev(bi);
								has_PPR_preds = true;
							}
							for (int ci : it_bi_pr_pred->second) {
								if (instr.accesses.find(ci) != instr.accesses.end()) {
									if (!has_PPR_preds || it_bi_ppr_pred->second.find(ci) == it_bi_ppr_pred->second.end()) {
										next.insert(ci);
									}
								}
							}
						}
					}
				}
			}
			// Swap the sets
			open = next;
			next = tmp;
			tmp = open;
			next.clear();
		}
	}
	else if (from_outside_instr) {
		if (instr.accesses.find(ai) == instr.accesses.end()) {
			moved_into = true;
			instr.accesses.insert(ai);
		}
	}
	// If ai ends up not having PPR-predecessors, it is a new bottom access
	if (!PPR[instr_id].contains_rev(ai) && (from_outside_instr || PR.contains_rev(ai))) {
		instr.bottom_accs.insert(instr.bottom_accs.end(), ai);
	}
	// If ai ends up not having PR-successors, it is a new top access
	if (!PPR[instr_id].contains(ai) && (from_outside_instr || PR.contains(ai))) {
		instr.top_accs.insert(instr.top_accs.end(), ai);
	}
	return moved_into;
}

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
	BiRelation PR;
	// Transitive closure of PR
	Relation PRplus;
	// PR relation at instruction level
	BiRelation PRinstr;
	// Dependency relation DP
	// Covers value and address dependencies, and RF for thread-local variables
	Relation DP;
	// CTRL dependency relation
	Relation CTRL;
	// CMP relation
	Relation CMP;
	
	// Various IndexedMaps to keep track of information extracted from the LTS
	IndexedMap<string> instruction_positions; // Maps short instruction position strings to integer IDs
	IndexedMap<string> instruction_ids; // Maps long instruction strings to integer IDs
	map<int, Instruction> instructions;
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
			string label = line.substr(sep1+2, sep2-(sep1+2));
			int tgt = stoi(line.substr(sep2+2, line.length()-(sep2+2)-1));
			// List of previous and current accesses, used to build intra-instruction PR-relation
			vector<int> prev_accesses, curr_accesses_bottom, curr_accesses_top;

			// Store long instruction string description
			int iid = instruction_ids.find(label);
			// Check if instruction is already stored. If not, create it
			if (iid == -1) {
				iid = instruction_ids.insert(label);
				cout << iid << ": " << label << endl;
				if (label.compare("tau") != 0) {
					//cout << label << endl;
					// Break label further down
					label = label.substr(3, label.length()-4);
					// cout << label << endl;
					sep1 = label.find_first_of(",");
					sep2 = label.find_first_of(",", sep1+1);
					string thread = label.substr(sep1+2, sep2-sep1-2);
					int tid = thread_ids.insert(thread);
					sep1 = label.find_first_of(",", sep2+1);
					string statement = label.substr(sep2+2, sep1-sep2-2);
					cout << statement << endl;
					int ipos = instruction_positions.insert(statement);

					// Set the instruction info
					instr.pos = ipos;
					instr.tid = tid;
					instr.is_guarded = false;
					instr.accesses.clear();
					instr.bottom_accs.clear();
					instr.cond_reads.clear();
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

							// Create and store read access
							int loc = location_ids.insert(read);
							acc.location = loc;
							// cout << loc << endl;
							// Is the variable thread-local? (encoded in name by the fact that ' occurs more than once)
							acc.local = count(read.begin(), read.end(), '\'') > 1;
							// cout << acc.local << endl;
							acc.type = READ;
							// cout << acc.type << endl;
							acc.instruction = ipos;
							// cout << acc.instruction << endl;
							acc.tid = tid;
							// cout << tid << endl;
							int aid = accesses.insert(acc);
							//cout << "read " << aid << " : " << read << ": " << label << endl;
							instr.accesses.insert(instr.accesses.end(), aid);
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

									// Store dependencies
									if (weakmemmodel == ARM) {
										DP.insert(aid, depaid);
									}
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
						// The instruction is guarded if there are no writes at this point
						if (writes.compare("[]") == 0) {
							instr.is_guarded = true;
							// Store additional reads to check the condition (besides those in bottom_accs), if needed
							if (!curr_accesses_top.empty()) {
								instr.cond_reads = curr_accesses_top;
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
							acc.instruction = ipos;
							// cout << acc.instruction << endl;
							acc.tid = tid;
							// cout << tid << endl;
							int aid = accesses.insert(acc);
							//cout << "write " << aid << " : " << write << ": " << label << endl;
							instr.accesses.insert(instr.accesses.end(), aid);
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
								if (reads_stored and weakmemmodel == ARM) {
									for (auto a : curr_accesses_bottom) {
										DP.insert(a, prev_accesses);
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
					instr.accesses.clear();
				}
				// Store the instruction
				auto it = instructions.insert(pair<int, Instruction>(iid, instr));
			}
			// Get the instruction
			auto it = instructions.find(iid);
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
		// for (auto i : PR) {
		// 	for (auto j : i.second) {
		// 		cout << "(" << i.first << ", " << j << ")" << endl;
		// 	}
		// }
		ltsfile.close();

		// For each instruction, create an access reorder relation (PPR, subrelation of PR, consisting of the PR-pairs safe under the weak memory model).
		// Initially, this is empty.
		vector<BiRelation> PPR(instructions.size());

		// Set of (instruction position, thread id) pairs of outgoing transitions of a state
		set<pair<int, int>> out;
		// Compute inter-instruction PR and PRinstr
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
				int instr_id = (*(lts_transitions[i].instruction)).first;
				int pos = instr.pos;
				int tid = instr.tid;
				for (int j = lts_states[tgt].outgoing_begin; j < lts_states[tgt].outgoing_end; j++) {
					int tgt_instr_id = (*(lts_transitions[j].instruction)).first;
					auto tgt_instr = (*(lts_transitions[j].instruction)).second;
					int tgt_pos = tgt_instr.pos;
					int tgt_tid = tgt_instr.tid;
					if (tgt_tid == tid) {
						if (out.find(pair<int, int>(tgt_pos, tgt_tid)) == out.end()) {
							// PR-relate top elements of instr with bottom elements of tgt_instr
							for (auto ta : instr.top_accs) {
								PR.insert(ta, tgt_instr.bottom_accs);
								PRinstr.insert(instr_id, tgt_instr_id);
							}
						}
					}
				}
			}
		}

		// Compute the RF relation for thread-local variables. This is integrated into DP.
		if (weakmemmodel == ARM) {
			set<int> open;
			set<int> closed;
			for (auto i : PR) {
				Access& a = accesses.get(i.first);
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
						Access& b = accesses.get(j);
						if (a.location != b.location || b.type == READ) {
							if (a.location == b.location) {
								DP.insert(j, i.first);
							}
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
		}

		// Compute PRplus via Floyd-Warshall
		PRplus.copy(PR);

		for (int k = 0; k < accesses.size(); k++) {
			for (int i = 0; i < accesses.size(); i++) {
				if (PRplus.contains(i) && PRplus.contains(k)) {
					auto ii = PRplus.get(i);
					auto ik = PRplus.get(k);
					for (int j = 0; j < accesses.size(); j++) {
						if (ii->second.find(k) != ii->second.end() && ik->second.find(j) != ik->second.end()) {
							PRplus.insert(i, j);
						}
					}
				}
			}
		}

		if (weakmemmodel == ARM) {
			// Using PRplus, compute the CTRL relation
			for (auto i : instructions) {
				if (i.second.is_guarded) {
					// The bottom accesses of i and those in cond_reads are the reads necessary to evaluate a condition
					for (auto ai : i.second.bottom_accs) {
						if (PRplus.contains(ai)) {
							auto it = PRplus.get(ai);
							for (auto aj : it->second) {
								CTRL.insert(aj, ai);
							}
						}
					}
					for (auto ai : i.second.cond_reads) {
						if (PRplus.contains(ai)) {
							auto it = PRplus.get(ai);
							for (auto aj : it->second) {
								CTRL.insert(aj, ai);
							}
						}
					}
				}
			}
		}

		// In each instruction, reorder accesses to obtain the PPR-relations
		set<int> set1, set2;
		set<int>& openset = set1;
		set<int>& tmpset = set1;
		set<int>& nextset = set2;
		for (auto instr : instructions) {
			openset.clear();
			nextset.clear();
			openset.insert(instr.second.bottom_accs.begin(), instr.second.bottom_accs.end());
			while (!openset.empty()) {
				for (int ai : openset) {
					reorder(ai, instr.first, instructions, accesses, weakmemmodel, PPR, PR, DP, CTRL, false);
					if (PR.contains(ai)) {
						auto it = PR.get(ai);
						for (int bi : it->second) {
							if (instr.second.accesses.find(bi) != instr.second.accesses.end()) {
								nextset.insert(bi);
							}
						}
					}
				}
				// Swap the sets
				openset = nextset;
				nextset = tmpset;
				tmpset = openset;
				nextset.clear();
			}
		}

		// Now reorder accesses across instructions
		vector<vector<int>> accvector1(instructions.size());
		vector<vector<int>> accvector2(instructions.size());
		vector<vector<int>>& newly_added_accesses = accvector1;
		vector<vector<int>>& next_added_accesses = accvector2;
		vector<vector<int>>& tmp_accesses = accvector1;

		for (auto instr : instructions) {
			openset.clear();
			nextset.clear();
			openset.insert(instr.second.bottom_accs.begin(), instr.second.bottom_accs.end());
			while (!openset.empty()) {
				for (int ai : openset) {
					newly_added_accesses[instr.first].insert(newly_added_accesses[instr.first].end(), ai);
					if (PPR[instr.first].contains(ai)) {
						auto it = PPR[instr.first].get(ai);
						for (int bi : it->second) {
							if (nextset.find(bi) == nextset.end()) {
								nextset.insert(bi);
							}
						}
					}
				}
				openset = nextset;
				nextset = tmpset;
				tmpset = openset;
				nextset.clear();
			}
		}

		openset.clear();
		nextset.clear();
		for (int i = 0; i < instructions.size(); i++) {
			openset.insert(i);
		}
		while (!openset.empty()) {
			for (int instr_id : openset) {
				if (PRinstr.contains(instr_id)) {
					auto instr_it = PRinstr.get(instr_id);
					for (int instr_id2 : instr_it->second) {
						if (!newly_added_accesses[instr_id2].empty()) {
							for (int ai : newly_added_accesses[instr_id2]) {
								auto instr = (instructions.find(instr_id))->second;
								if (instr.accesses.find(ai) == instr.accesses.end()) {
									int result = reorder(ai, instr_id, instructions, accesses, weakmemmodel, PPR, PR, DP, CTRL, true);
									if (result) {
										if (next_added_accesses[instr_id].empty()) {
											if (PRinstr.contains_rev(instr_id)) {
												auto instr_it2 = PRinstr.get_rev(instr_id);
												nextset.insert(instr_it2->second.begin(), instr_it2->second.end());
											}
										}
										next_added_accesses[instr_id].insert(next_added_accesses[instr_id].end(), ai);
									}
								}
							}
						}
					}
				}
			}
			// Swap
			openset = nextset;
			nextset = tmpset;
			tmpset = openset;
			nextset.clear();
			newly_added_accesses = next_added_accesses;
			next_added_accesses = tmp_accesses;
			tmp_accesses = newly_added_accesses;
			for (int i = 0; i < instructions.size(); i++) {
				next_added_accesses[i].clear();
			}
		}

		cout << "PR:" << endl;
		for (auto i : PR) {
			for (auto j : i.second) {
				cout << "(" << i.first << ", " << j << ")" << endl;
			}
		}
		cout << "The PPRs: " << endl;
		for (int i = 0; i < instructions.size(); i++) {
			for (auto i : PPR[i]) {
				for (auto j : i.second) {
					cout << "(" << i.first << ", " << j << ")" << endl;
				}
			}
		}
		// cout << "PRplus:" << endl;
		// for (auto i : PRplus) {
		// 	for (auto j : i.second) {
		// 		cout << "(" << i.first << ", " << j << ")" << endl;
		// 	}
		// }
		// cout << "DP:" << endl;
		// for (auto i : DP) {
		// 	for (auto j : i.second) {
		// 		cout << "(" << i.first << ", " << j << ")" << endl;
		// 	}
		// }
		// cout << "CTRL:" << endl;
		// for (auto i : CTRL) {
		// 	for (auto j : i.second) {
		// 		cout << "(" << i.first << ", " << j << ")" << endl;
		// 	}
		// }
		cout << "PRinstr:" << endl;
		for (auto i : PRinstr) {
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

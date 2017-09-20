import os

# minimisation of LTSs using mcrl2
WEAK_BISIM = 'weak-bisim'
BRANCHING_BISIM = 'branching-bisim'
ltsconvert = 'ltsconvert -eNAME %s %s %s'
	
def minimize(input, output, equivalence):
	cmd_reduce = ltsconvert % (equivalence, input, output)
	os.system(cmd_reduce)
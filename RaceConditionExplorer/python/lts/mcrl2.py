import subprocess
import logging
from lts import LTS

_equivalence_dict = {   LTS.Equivalence.WEAK_BISIM      : 'weak-bisim',
						LTS.Equivalence.BRANCHING_BISIM : 'branching-bisim'
					}

# minimisation of LTSs using mcrl2
ltsconvert = 'ltsconvert -e%s %s %s'
	
def minimize(input, output, equivalence):
	equivalence = _equivalence_dict[equivalence]
	cmd_reduce = ltsconvert % (equivalence, input, output)
	proc = subprocess.run(cmd_reduce, stderr=subprocess.PIPE, universal_newlines=True)
	if proc.returncode != 0:
		logging.error("ltsconvert reports: "+ str(proc.stderr))
		raise subprocess.CalledProcessError(proc.returncode, cmd_reduce, stderr=proc.stderr)
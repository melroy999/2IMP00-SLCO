# init file allows to switch back-ends

# minimize function
from .mcrl2 import minimize # from mcrl2

# read and write functions
from .aut import read, write # from aut

from .lts import *
from .AutLTS import AutLTS

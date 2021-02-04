from sage.all import Infinity

from multiprocessing import cpu_count

libcrunch = None
ncpus = cpu_count()
normaliz = None
debug = False
disklist = False

symbolic = False

dict_polynomial = True
save_memory = False

_alt_ncpus = None
optimisation_level = 1
addmany_dispatcher = 'numerator'
addmany_optimise = True
symbolic_count_varieties = []

_simplify_bound = Infinity

# The plumber tries to prevent leaks. He does this by e.g. avoiding libsingular.
plumber = True

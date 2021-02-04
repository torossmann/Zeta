libcrunch = None
from multiprocessing import cpu_count
ncpus = cpu_count()
normaliz = None
debug = False
disklist = False

# The plumber tries to prevent leaks. He does this by e.g. avoiding libsingular.
plumber = True

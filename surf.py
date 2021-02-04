"""
Fast arithmetic with simplicial univariate rational functions.
"""

from sage.all import *

from collections import namedtuple

from array import array

import ctypes, gzip, struct

import common

from util import create_logger
logger = create_logger(__name__)

#
# Try to load the C cruncher. If that fails, we'll use a Python implementation.
#
from pkg_resources import resource_exists, resource_filename
try:
    if resource_exists('Zeta', 'crunch.so'):
        common.libcrunch = ctypes.CDLL(resource_filename('Zeta', 'crunch.so'))
except:
    pass

# [S]implicial [U]nivariate [R]ational [F]unctions are expressions of the
# form scalar / prod(rays[i][0]*s - rays[i][1], i=1,...,e).

SURF = namedtuple('SURF', ['scalar', 'rays'])

_BUFSIZE = 32*1024*1024

INTSIZE = 4
if array('i').itemsize != INTSIZE:
    raise ArithmeticError('Need sizeof(int) == 4')

class SURFSum:
    def __init__(self, filename, compresslevel=9):
        self._filename = filename
        self._meta_filename = filename + '.meta'
        self._compresslevel = compresslevel

        try:
            f = open(self._meta_filename, 'rb')
        except IOError:
            # No metadata -> start from scratch.
            self._critical = set()
            self._cand = dict()
            self._count = 0
            self._file = gzip.open(filename, 'wb', compresslevel)
        else:
            # Recover metadata and open file for appending.
            with f:
                D = loads(f.read())
            self._cand, self._critical, self._count = D['cand'], D['critical'], D['count']
            self._file = gzip.open(filename, 'ab', compresslevel)

    def __str__(self):
        return 'Sum of %d SURFs [%d critical points]' % (self._count, len(self._critical))

    def close(self):
        # Flush data file and write metadata.
        if not self._file.closed:
            self._file.close()
        with open(self._meta_filename, 'wb') as f:
            f.write(dumps(
                    { 'cand':     self._cand,
                      'critical': self._critical,
                      'count':    self._count }
                    ))

    def add(self, S):
        if self._file.closed:
            raise RuntimeError('Lost access to the SURFSum file')

        self._count += 1

        # Binary format:
        # k scalar a[0] b[0] a[1] b[1] ... a[k-1] b[k-1]
        raw = map(int, [len(S.rays), S.scalar] + flatten(S.rays))
        self._file.write(array('i', raw).tostring())

        # Update the candidate denominator.
        E = {}
        for (a,b) in S.rays:
            if a == 0:
                continue

            self._critical.add(QQ(b)/QQ(a))

            # Only consider a*s-b with gcd(a,b) = 1 and a > 0.
            g = int(gcd((a, b)))
            a,b = a/g, b/g

            if a < 0:
                a,b = -a, -b

            # (possible) TODO:
            # Get rid of things like s+1 that cannot show up in the final
            # result.

            if E.has_key((a,b)):
                E[(a,b)] += 1
            else:
                E[(a,b)] = 1

        # Now 'E' gives the multiplicities of candidate terms for S.
        # We take the largest multiplicities over all 'S'.
        for r in E.keys():
            if (not self._cand.has_key(r)) or self._cand[r] < E[r]:
                self._cand[r] = E[r]

def _crunch_c(args):
    argc = int(len(args))
    argv = (ctypes.c_char_p*int(argc))()
    for i in xrange(argc):
        argv[i] = args[i]
    return common.libcrunch.crunch(argc,argv)

# A python implementation of `crunch.c'.
def _crunch_py(argv):

    if len(argv) < 4: return 1

    with open(argv[1], 'r') as file:
        nvalues = int(file.readline())
        values = [QQ(v) for v in file]

    if len(values) != nvalues: return 1

    results = nvalues * [QQ(0)]

    for dfile in argv[3:]:
        with gzip.open(dfile, 'rb') as gzfile:
            gzfile._read_eof = lambda *args: None # ignore gzip CRC errors in streams

            while True:
                raw = gzfile.read(INTSIZE)
                if not raw:
                    break # EOF

                if len(raw) != INTSIZE: return 1

                nrays, = struct.unpack('i', raw)
                chunk_size = 2*nrays + 1

                raw = gzfile.read(chunk_size * INTSIZE)
                if len(raw) != chunk_size * INTSIZE: return 1
                chunk = [QQ(v) for v in struct.unpack('i' * chunk_size, raw)]
                
                for i in xrange(nvalues):
                    results[i] += chunk[0] / prod(chunk[j]*values[i] - chunk[j+1] for j in xrange(1,chunk_size,2))

    with open(argv[2], 'w') as file:
        for r in results:
            file.write(str(r) + '\n')
    return 0

def crunch(args):
    return _crunch_c(args) if common.libcrunch else _crunch_py(args)

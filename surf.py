"""
Fast arithmetic with simplicial univariate rational functions.
"""
from sage.all import QQ, loads, dumps, factor, flatten, gcd, prod, SR
from sage.parallel.decorate import parallel
from sage.cpython.string import str_to_bytes

from collections import namedtuple
from array import array
from pkg_resources import resource_exists, resource_filename

import os
import ctypes
import gzip
import struct

from . import common

from .util import create_logger, TemporaryDirectory, readable_filesize
logger = create_logger(__name__)

#
# Try to load the C cruncher. If that fails, we'll use a Python implementation.
#
try:
    if resource_exists('Zeta', 'crunch.so'):
        common.libcrunch = ctypes.CDLL(resource_filename('Zeta', 'crunch.so'))
except:
    pass

# [S]implicial [U]nivariate [R]ational [F]unctions are expressions of the
# form scalar / prod(rays[i][0]*s - rays[i][1], i=1,...,e).

SURF = namedtuple('SURF', ['scalar', 'rays'])


class SURFError(Exception):
    pass


_BUFSIZE = 32 * 1024 * 1024
INTSIZE = 4

if array('i').itemsize != INTSIZE:
    raise SURFError('Need sizeof(int) == 4')


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
                    {'cand': self._cand,
                     'critical': self._critical,
                     'count': self._count}
                    ))

    def add(self, S):
        if self._file.closed:
            raise SURFError('Lost access to the SURFSum file')

        self._count += 1

        # Binary format:
        # k scalar a[0] b[0] a[1] b[1] ... a[k-1] b[k-1]

        # NOTE:
        # In rare cases, we can run into numbers that don't fit into 32-bit
        # integers. We then use an ad hoc hack to reduce to smaller numbers.
        # To trigger this, count ideals in L(6,11).

        raw = list(map(int, [len(S.rays), S.scalar]))
        for a, b in S.rays:
            try:
                _ = array('i', [int(a), int(b)])
                raw.extend([int(a), int(b)])
            except OverflowError:
                if a:
                    raise SURFError('Ray does not fit into a pair of 32-bit integers')
            else:
                continue

            fac = factor(b)
            li = flatten([[p] * e for (p, e) in fac])
            li[0] *= fac.unit()
            # assert b == prod(li)
            if len(li) % 2 == 0:
                li[0] = -li[0]
            # assert -b == prod(-c for c in li)
            for c in li:
                raw.extend([int(0), int(c)])
            raw[0] += len(li) - 1

        try:
            self._file.write(array('i', raw).tobytes())
        except OverflowError:
            raise SURFError('Number too large to fit into a 32-bit integer')

        # Update the candidate denominator.
        E = {}
        for a, b in S.rays:
            if a == 0:
                continue

            self._critical.add(QQ(b) / QQ(a))

            # Only consider a*s-b with gcd(a,b) = 1 and a > 0.
            g = int(gcd((a, b)))
            a, b = a // g, b // g

            if a < 0:
                a, b = -a, -b

            # (possible, depending on the counting problem) TODO:
            # Get rid of things like s+1 (for subobjects) that cannot show up
            # in the final result.

            if (a, b) in E:
                E[(a, b)] += 1
            else:
                E[(a, b)] = 1

        # Now 'E' gives the multiplicities of candidate terms for S.
        # We take the largest multiplicities over all 'S'.
        for r in E:
            if r not in self._cand or self._cand[r] < E[r]:
                self._cand[r] = E[r]


def _crunch_c(args):
    argc = int(len(args))
    argv = (ctypes.c_char_p * int(argc))()
    for i in range(argc):
        argv[i] = str_to_bytes(args[i])
    return common.libcrunch.crunch(argc, argv)


# A python implementation of `crunch.c'.
def _crunch_py(argv):
    if len(argv) < 4:
        return 1

    with open(argv[1], 'r') as file:
        nvalues = int(file.readline())
        values = [QQ(v) for v in file]

    if len(values) != nvalues:
        return 1

    results = nvalues * [QQ(0)]

    for dfile in argv[3:]:
        with gzip.open(dfile, 'rb') as gzfile:
            gzfile._read_eof = lambda *args: None  # ignore gzip CRC errors in streams

            while True:
                try:
                    raw = gzfile.read(INTSIZE)
                except EOFError:
                    break

                if not raw:
                    break  # EOF

                if len(raw) != INTSIZE:
                    return 1

                nrays, = struct.unpack('i', raw)

                chunk_size = 2 * nrays + 1
                raw = gzfile.read(chunk_size * INTSIZE)

                if len(raw) != chunk_size * INTSIZE:
                    return 1
                chunk = [QQ(v) for v in struct.unpack('i' * chunk_size, raw)]

                for i in range(nvalues):
                    results[i] += chunk[0] / prod(chunk[j] * values[i] - chunk[j + 1] for j in range(1, chunk_size, 2))

    with open(argv[2], 'w') as file:
        for r in results:
            file.write(str(r) + '\n')
    return 0


def crunch(args):
    return _crunch_c(args) if common.libcrunch else _crunch_py(args)


def multicrunch(surfsums, varname=None):
    """
    Given an iterable consisting of SURFSums, compute the rational function
    given by their combined sum.
    Note that this rational function necessarily has degree <= 0.
    """

    surfsums = list(surfsums)

    #
    # Combine the various critical sets and construct a candidate denominator.
    #

    critical = set().union(*(Q._critical for Q in surfsums))
    cand = dict()
    for Q in surfsums:
        E = Q._cand
        for r in E:
            if r not in cand or cand[r] < E[r]:
                cand[r] = E[r]

    if varname is None:
        varname = 's'

    R = QQ[varname]
    s = R.gen(0)
    g = R(prod((a * s - b)**e for ((a, b), e) in cand.items()))
    m = g.degree()

    logger.info('Total number of SURFs: %d' % sum(Q._count for Q in surfsums))

    for Q in surfsums:
        Q._file.flush()

    logger.info('Combined size of data files: %s' %
                readable_filesize(sum(os.path.getsize(Q._filename)
                                      for Q in surfsums)))
    logger.info('Number of critical points: %d' % len(critical))
    logger.info('Degree of candidate denominator: %d' % m)

    #
    # Construct m + 1 non-critical points for evaluation.
    #

    values = set()
    while len(values) < m + 1:
        x = QQ.random_element()
        if x in critical:
            continue
        values.add(x)
    values = list(values)

    #
    # Set up parallel computations.
    #

    # bucket_size = ceil(float(len(values)) / common.ncpus)
    # this was unused

    dat_filenames = [Q._filename for Q in surfsums]

    res_names = []
    val_names = []

    value_batches = [values[j::common.ncpus] for j in range(common.ncpus)]

    with TemporaryDirectory() as tmpdir:
        for j, v in enumerate(value_batches):
            if not v:
                break

            val_filename = os.path.join(tmpdir, 'values%d' % j)
            val_names.append(val_filename)
            res_names.append(os.path.join(tmpdir, 'results%d' % j))
            with open(val_filename, 'w') as val_file:
                val_file.write(str(len(v)) + '\n')
                for x in v:
                    val_file.write(str(x) + '\n')

        def fun(k):
            ret = crunch(['crunch', val_names[k], res_names[k]] + dat_filenames)
            if ret == 0:
                logger.info('Cruncher #%d finished.' % k)
            return ret

        logger.info('Launching %d crunchers.' % len(res_names))

        if not common.debug:
            fun = parallel(ncpus=len(res_names))(fun)
            for (arg, ret) in fun(list(range(len(res_names)))):
                if ret == 'NO DATA':
                    raise RuntimeError('A parallel process died')
                if ret != 0:
                    raise RuntimeError('crunch failed')
        else:
            for k in range(len(res_names)):
                fun(k)

        #
        # Collect results
        #
        pairs = []

        for j, rn in enumerate(res_names):
            it_batch = iter(value_batches[j])
            with open(rn, 'r') as res_file:
                for line in res_file:
                    # We also need to evaluate the candidate denominator 'g'
                    # from above at the given random points.
                    x = QQ(next(it_batch))
                    pairs.append((x, g(x) * QQ(line)))

    if len(values) != len(pairs):
        raise RuntimeError('Length of results is off')

    f = R.lagrange_polynomial(list(pairs))
    res = SR(f / g)
    return res.factor() if res else res

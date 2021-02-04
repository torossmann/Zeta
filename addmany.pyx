import common
import sage.all
import sage.interfaces
import sage.parallel
import os
import sys
import itertools
import random
import struct

from sage.all import Integer, Rational, FractionField

from tmplist import DiskList
from collections import Counter

from util import create_logger
logger = create_logger(__name__)

BUCKET_SIZE = 64

import bz2
Open = bz2.BZ2File
# Open = lambda name, mode: open(name, mode, 0x100000)

from libc.stdint cimport int64_t, uint32_t, uint64_t

from sage.libs.gmp.all cimport *

cdef class HashAdder:
    cdef dict D, simple
    cdef object func

    def __init__(HashAdder self, func):
        self.D = {}
        self.simple = {}
        self.func = func

    def __len__(HashAdder self):
        return len(self.D)

    def __getitem__(HashAdder self, key):
        return self.D[key]

    def __setitem__(HashAdder self, key, value):
        self.D[key] = value
        self.simple[key] = False
        
    def __delitem__(HashAdder self, key):
        del self.D[key]
        del self.simple[key]

    def __contains__(HashAdder self, key):
        return key in self.D

    cdef add(HashAdder self, value, key=None, simple=False):
        if key is None:
            key = self.func(value)

        if key not in self.D:
            self.D[key] = value
            self.simple[key] = simple
        else:
            self.D[key] += value
            self.simple[key] = False

    cdef addmany(HashAdder self, iterable):
        for value in iterable:
            self.add(value)

    def simplify(HashAdder self):
        cdef bint done = False

        while not done:
            done = True
            for key in self.D:
                # Only keep things that evaluate to 'True'.
                if not self.D[key]:
                    del self.D[key]
                    del self.simple[key]
                    done = False
                    break  # Since we deleted a key, we should abort iterating over self.D.

                if self.simple[key]:
                    continue

                new_value = self.D[key].simplify()
                new_key = self.func(new_value)

                if new_key == key or (new_key not in self.D):
                    self.D[key] = new_value
                    self.simple[key] = True
                else:
                    del self.D[key]
                    del self.simple[key]
                    self.D[new_key] += new_value
                    self.simple[new_key] = False
                    done = False
                    break

    cdef values(HashAdder self):
        return self.D.itervalues()

    def keys(HashAdder self):
        return self.D.iterkeys()

    cdef items(HashAdder self):
        return self.D.iteritems()

    def __iter__(HashAdder self):
        return self.D.iterkeys()

# A term a * x^e[0] * y^e[1] for a = n/d (n > 0) is stored using exactly 36
# bytes as follows:
#   - e[0] + (e[1] << 16) (uint32_t)
#   - lowest, highest 64-bits of n (2 * uint64_t)
#   - lowest 64-bits of abs(d) (uint64_t)
#   - is_nonnegative(d) + (abs(highest 64-bits of abs(d))<<1) (uint64_t)
cdef enum:
        _string_length = 36

if sizeof(uintmax_t) != sizeof(uint64_t):
    raise RuntimeError("Zeta requires sizeof(uintmax_t) == sizeof(uint64_t)")

cdef class Rational256:
    cdef uint64_t n_lo, n_hi, d_lo, d_hi

    def __init__(Rational256 self, x=None):
        if x is None:
            x = Rational(0)
        n, d = long(x.numerator()), long(x.denominator())
        if n < 0:
            n = -n
            d = -d

        cdef bint is_negative = (d < 0)
        d = -d if is_negative else d

        self.n_lo = n & 0xffffffffffffffffULL # 2^64-1
        self.n_hi = n >> 64
        self.d_lo = d & 0xffffffffffffffffULL
        self.d_hi = d >> 64

        if self.d_hi & 0x8000000000000000ULL: # check if the 2^63 bit is set
            raise OverflowError('denominator does not fit into 128 bits')
        self.d_hi = (self.d_hi << 1) | (1 if is_negative else 0)

    def dumps(Rational256 self):
        return struct.pack('=QQQQ', self.n_lo, self.n_hi, self.d_lo, self.d_hi)

    def loads(Rational256 self, str s):
        self.n_lo, self.n_hi, self.d_lo, self.d_hi = struct.unpack('=QQQQ', s)

    def __nonero__(Rational256 self):
        return self.n_lo == 0 and self.n_hi == 0

    cdef to_mpq_t(Rational256 self, mpq_t x):
        cdef mpz_t a, b
        cdef bint is_negative

        cdef uint64_t d_hi_shifted = self.d_hi >> 1

        mpz_init(a) ; mpz_init(b)

        is_negative = self.d_hi & 1

        if self.n_hi:
            mpz_set_ux(a, self.n_lo)
            mpz_set_ux(b, self.n_hi)
            mpz_mul_2exp(b, b, 64)
            mpz_ior(mpq_numref(x), a, b)
        else:
            mpz_set_ux(mpq_numref(x), self.n_lo)

        if d_hi_shifted:
            mpz_set_ux(a, self.d_lo)
            mpz_set_ux(b, d_hi_shifted)
            mpz_mul_2exp(b, b, 64)
            mpz_ior(mpq_denref(x), a, b)
        else:
            mpz_set_ux(mpq_denref(x), self.d_lo)

        # mpq_canonicalize(x) # not needed!

        if is_negative:
            mpq_neg(x, x)
            
        mpz_clear(a) ; mpz_clear(b)

    cdef from_mpq_t(Rational256 self, mpq_t x):
        cdef int sgn
        cdef mpz_t a, b, c

        sgn = mpq_sgn(x)

        if not sgn:
            self.n_lo = self.n_hi = self.d_hi = 0
            self.d_lo = 1
            return

        mpz_init(a) ; mpz_init(b) ; mpz_init(c)

        #### a = abs(x.numerator())
        mpz_set(a, mpq_numref(x))
        if sgn == -1: # NOTE: denominators of canonicalised rational numbers are positive
            mpz_neg(a, a)

        #### self.n_lo = b = a & (2^64 - 1)
        mpz_set_ux(c, 0xffffffffffffffffULL)
        mpz_and(b, a, c)
        self.n_lo = mpz_get_ux(b)

        #### self.n_hi = b = a >> 64
        mpz_fdiv_q_2exp(b, a, 64)
        self.n_hi = mpz_get_ux(b)

        #### b = a >> 128
        mpz_fdiv_q_2exp(b, b, 64)
        if mpz_sgn(b):
            raise OverflowError('Numerator does not fit into 128 bits')

        #### a = x.denominator()
        mpz_set(a, mpq_denref(x))

        #### self.d_lo = b = a & (2^64 - 1)
        mpz_and(b, a, c)
        self.d_lo = mpz_get_ux(b)

        #### b = a >> 64
        mpz_fdiv_q_2exp(b, a, 64)
        if mpz_tstbit(b, 63):
            raise OverflowError('Denominator does not fit into 128 bits [sign]')

        ####  self.d_hi = b = ((a >> 64) << 1) | is_negative
        mpz_mul_2exp(b, b, 1)
        mpz_set_ui(c, 1 if sgn == -1 else 0)
        mpz_ior(b, b, c)
        self.d_hi = mpz_get_ux(b)

        ### b = a >> 128
        mpz_fdiv_q_2exp(b, b, 64)
        if mpz_sgn(b):
            raise OverflowError('Denominator does not fit into 128 bits [size]')

        mpz_clear(a) ; mpz_clear(b) ; mpz_clear(c)

    def __add__(Rational256 self, Rational256 other):
        # return Rational256(self.eval() + other.eval())
        cdef Rational256 x = Rational256.__new__(Rational256)
        cdef mpq_t a, b

        mpq_init(a) ; mpq_init(b)

        self.to_mpq_t(a)
        other.to_mpq_t(b)
        mpq_add(a, a, b)
        x.from_mpq_t(a)

        mpq_clear(a) ; mpq_clear(b)
        return x

    def eval(Rational256 self):
        cdef uint64_t d_hi = self.d_hi
        cdef bint is_negative
        cdef int64_t d64 = 0

        is_negative = d_hi & 1
        d_hi >>= 1

        if d_hi or self.d_lo & 0x8000000000000000ULL:
            d = Integer(self.d_lo) | (Integer(d_hi) << 64)
            d = -d if is_negative else d
        else:
            # +/- [d_hi|d_lo] fits into a signed(!) 64-bit integer.
            d64 = -self.d_lo if is_negative else self.d_lo
            d = Integer(d64)

        return ((Integer(self.n_lo) | (Integer(self.n_hi) << 64)) if self.n_hi else Integer(self.n_lo))/d

cdef class DictPolynomial:
    cdef dict D

    def __init__(DictPolynomial self, f=None):
        cdef uint32_t key

        self.D = {}

        if isinstance(f, dict):
            self.D = f
        elif hasattr(f, 'read'):
            self.load(f)
        elif hasattr(f, 'exponents'):
            for c, alpha in itertools.izip(f.coefficients(), f.exponents()):
                if len(alpha) != 2:
                    raise NotImplementedError('DictPolynomial only supports bivariate polynomials')
                if alpha[0] < 0 or alpha[0] > 0xffff or alpha[1] < 0 or alpha[1] > 0xffff:
                    raise ValueError('exponents do not fit into 16 bits')
                key = alpha[0] + (alpha[1] << 16)
                self.D[key] = Rational256(c)

    def _add_key_value(DictPolynomial self, uint32_t key, value):
        try:
            a = self.D[key] + value
        except KeyError:
            self.D[key] = value
            return

        if not a:
            del self.D[key]
        else:
            self.D[key] = a
                
    def __iadd__(DictPolynomial self, DictPolynomial other):
        cdef uint32_t key
        for key, value in other.D.iteritems():
            self._add_key_value(key, value)
        return self
   
    def polynomial(DictPolynomial self, ring):
        cdef uint32_t key
        y, x = ring.gens() # at some point, I decided to order variables as (t,q) instead of (q,t)
        return ring.sum(value.eval() * y**(key & 0xffff) * x**(key >> 16) for key, value in self.D.iteritems())

    def dump(DictPolynomial self, file):
        cdef uint32_t key
        for key, value in self.D.iteritems():
            file.write(struct.pack('=I', key) + value.dumps())

    def _terms_from_file(DictPolynomial self, file):
        cdef uint32_t key
        cdef Rational256 x
        cdef str raw

        while True:
            raw = file.read(_string_length)
            if not raw:
                return
            if len(raw) != _string_length:
                raise RuntimeError

            key, = struct.unpack('=I',raw[:4])
            x = Rational256()
            x.loads(raw[4:])
            yield key, x
   
    def add_from_file(DictPolynomial self, file):
        cdef uint32_t key
        cdef Rational256 value

        for key, value in self._terms_from_file(file):
            self._add_key_value(key, value)

    def load(DictPolynomial self, file):
        for key, value in self._terms_from_file(file):
            self.D[key] = value

def _addmany_numerator(filenames, denominator, *args):
    cdef str tmpdir = os.path.dirname(filenames[0])

    # Read all CRFs into memory. If that's a problem, then we're in more
    # serious trouble.
    cdef list all_crfs = list(itertools.chain.from_iterable(DiskList(f) for f in filenames))
    for f in filenames:
        DiskList(f).unlink()

    common_denominator = denominator.evaluate_reciprocal()

    def add(k):
        cdef DictPolynomial res, dp, z
        cdef int i, j, pid

        R = denominator.ring
        K = FractionField(R)
        res = DictPolynomial()

        if not common.save_memory:
            for a in itertools.islice(all_crfs, k, None, common.ncpus):
                try:
                    a_in_K =  K.coerce(a.evaluate())
                except TypeError:
                    raise ValueError('this example is not uniform: use the symbolic dispatcher instead')
                num, den = a_in_K.numerator(), a_in_K.denominator()
                res += DictPolynomial(R.product(num, common_denominator // den))
            with Open(os.path.join(tmpdir, 'res%d' % k), 'wb') as f:
                res.dump(f)
            logger.info('Summator #%d finished.' % k)
            return

        indices = range(k, len(all_crfs), common.ncpus)
        for i in xrange(0, len(indices), BUCKET_SIZE):
            pid = os.fork()
            if not pid:
                import sage.misc.misc; reload(sage.misc.misc)
                sage.interfaces.quit.invalidate_all()

                try:
                    try:
                        os.remove(os.path.join(tmpdir, 'fun%d' % k))
                    except OSError:
                        pass

                    dp = DictPolynomial()
                    for j in xrange(i, i + BUCKET_SIZE):
                        if j >= len(indices):
                            break
                        a_in_K =  K.coerce(all_crfs[indices[j]].evaluate())

                        num, den = a_in_K.numerator(), a_in_K.denominator()
                        dp += DictPolynomial(R.product(num, common_denominator // den))

                    with Open(os.path.join(tmpdir, 'fun%d' % k), 'wb') as f:
                        dp.dump(f)

                    os._exit(0)
                except Exception as e:
                    print >>sys.stderr, 'Unhandled exception in forked process:', e
                    sys.stderr.flush()
                    os._exit(1)
            else:
                _, status = os.waitpid(pid, 0)
                if status:
                    raise RuntimeError('The forked process of summator %d died with exit code %d.' % (k, status))
                with Open(os.path.join(tmpdir, 'fun%d' % k), 'rb') as f:
                    res.add_from_file(f)

        with Open(os.path.join(tmpdir, 'res%d' % k), 'wb') as f:
            res.dump(f)
        logger.info('Summator #%d finished.' % k)

    R = denominator.ring
    res = DictPolynomial()
    logger.info('Launching %d summators.' % common.ncpus)

    ET = sage.parallel.decorate.parallel(p_iter='reference' if common.debug else 'fork', ncpus=common.ncpus)(add)
    for (arg, ret) in ET(range(common.ncpus)):
        if ret == 'NO DATA':
            raise RuntimeError('A parallel process died.')
        with Open(os.path.join(tmpdir, 'res%d' % arg[0]), 'rb') as f:
            res.add_from_file(f)

    logger.info('All summators finished.')
    return res.polynomial(R) / denominator.evaluate_reciprocal()

def _addmany_symbolic(filenames, *args):
    def add(k):
        cnt = 0
        res = sage.all.SR(0)
        for f in filenames[k::common.ncpus]:
            Q = DiskList(f)
            for a in Q:
                z =  sage.all.SR(a.evaluate('symbolic'))
                z = z.factor() if z else z
                res += z
                cnt += 1
                # if cnt % 8 == 0 and res:
                #    res = res.factor()
        res = res.factor() if res else res
        logger.info('Summator #%d finished.' % k)
        return res

    res = sage.all.SR(0)
    logger.info('Launching %d summators.' % common.ncpus)
    ET = sage.parallel.decorate.parallel(p_iter='reference' if common.debug else 'fork', ncpus=common.ncpus)(add)
    for (arg, ret) in ET(range(common.ncpus)):
        if ret == 'NO DATA':
            raise RuntimeError('A parallel process died.')
        res += ret
    logger.info('All summators finished.')
    return res

def addmany(filenames, denominator):
    dispatcher = { 'symbolic': _addmany_symbolic, 'numerator': _addmany_numerator }
    method = common.addmany_dispatcher
    if method not in dispatcher:
         raise ValueError('invalid dispatcher')
    logger.info('addmany dispatcher: %s' % method)
    return dispatcher[method](filenames, denominator)  # (filenames, denominator if purged_denominator is None else purged_denominator, bound_t, bound_q)

# Merge CRFs with the same denominator.    
def _optimise_match(filenames):
    logger.info('Total number of rational functions: %d' % sum(len(DiskList(f)) for f in filenames))

    tmpdir = os.path.dirname(filenames[0])

    Q = []
    fp = lambda cr: tuple(tuple(e) for e in cr.exponents[1:])
    stats = Counter(fp(cr) for cr in itertools.chain.from_iterable(DiskList(f) for f in filenames))

    logger.debug('Total number of denominators = %d, maximal multiplicity = %d, number of singletons = %d' % (len(stats),
                                                                                                             max(stats.values()),
                                                                                                             sum(1 for v in stats if stats[v] == 1)))
    logger.debug('Joining rational functions.')
    D = {}

    new_filenames = [os.path.join(tmpdir, 'opt_match_eval%d' % k) for k in xrange(common.ncpus)]
    Q = [DiskList(f) for f in new_filenames]

    idx = 0
    for cr in itertools.chain.from_iterable(DiskList(f) for f in filenames):
        thumb = fp(cr)
        if thumb not in D:
            D[thumb] = cr
        else:
            D[thumb] += cr

        # NOTE: we don't take into account that after summation and
        # cancellation, the fingerprint might change. We simply add
        # all CRFs with the same fingerprint together (detecting zero).

        if not D[thumb]:
            del D[thumb]

        stats[thumb] -= 1

        if not stats[thumb]:
            del stats[thumb]
            if thumb in D:
                Q[idx].append(D[thumb])
                del D[thumb]
            idx = (idx + 1) % common.ncpus

    for f in filenames:
        DiskList(f).unlink()

    logger.debug('New number of rational functions: %d' % sum(1 for cr in itertools.chain.from_iterable(DiskList(f) for f in new_filenames)))
    return new_filenames

# Add CRFs according to various criteria.
def _optimise_combine(filenames):
    logger.info('Total number of rational functions: %d' % sum(len(DiskList(f)) for f in filenames))
    logger.debug('Reading all rational functions into system memory.')
    fingerprint = lambda cr: tuple(tuple(e) for e in cr.exponents[1:])

    HA = HashAdder(fingerprint)
    HA.addmany(itertools.chain.from_iterable(DiskList(f) for f in filenames))

    HA.simplify()

    def judge(r):
        return sum(1 for x in HA if r in x)

    def process(HA, sorter, selector):
        cnt = 0
        while True:
            cnt += 1

            for ray in sorter(HA):
                keys = [x for x in HA if ray in x]
                if len(keys) > 1 and selector(HA, ray, keys):
                    break
            else:
                break

            # If necessary, reduce the number of CRFs to be added in one
            # step by taking a random choice of at most 42 (magic constant!)
            # elements.
            indices = range(len(keys))
            random.shuffle(indices)
            indices = indices[:42]
            keys = [keys[i] for i in indices]

            logger.debug('Chosen ray %s, attained %d times.' % (ray, len(keys)))
            key = keys[0]
            value = HA[key]
            for x in keys[1:]:
                HA[key] += HA[x]
                del HA[x]
            
            if cnt % 3 == 0:
                cnt = 0
                HA.simplify()
            logger.debug('New total number: %d.' % len(HA))

    HA.simplify()
    rays_of = lambda HA: list(set(x for v in HA.keys() for x in v))
    
    def multiplicity_sorter_increasing(HA):
        rays = rays_of(HA)
        rays.sort(key=lambda ray: sum(1 for x in HA if ray in x))
        return rays

    def weight_sorter_decreasing(HA):
        rays = rays_of(HA)
        rays.sort(key=lambda x: -abs(x[0])-abs(x[1]))
        return rays

    def sum_sorter_increasing(HA):
        rays = rays_of(HA)
        rays.sort(key=lambda x: x[0] + x[1])
        return rays

    # def multiplicity_sorter_decreasing(HA):
    #     rays = multiplicity_sorter_increasing(HA)
    #     rays.reverse()
    #     return rays

    # def weight_sorter_increasing(HA):
    #     rays = rays_of(HA)
    #     rays.sort(key=lambda x: abs(x[0]) + abs(x[1]))
    #     return rays

    def pred_sum_sorter_increasing(HA, ray, keys):
        return ((ray[0] < 0) or (ray[1] < 0)) and len(keys) <= 1024 and len(keys) <= 64 * common.optimisation_level

    def pred_not_too_many(HA, ray, keys):
        return len(keys) <= 64 * common.optimisation_level

    strategies =  [
        ( 'Combining rays with negative entries and moderate multiplicities',
           sum_sorter_increasing, pred_sum_sorter_increasing ),

        ( 'Combining rays with low multiplicities',
          multiplicity_sorter_increasing, pred_not_too_many ),
        
        ( 'Combining rays with high weights and moderate multiplicities',
          weight_sorter_decreasing, pred_not_too_many ),
        ]

    for (descr, sorter, selector) in strategies:
        logger.debug('Optimising: %s.' % descr)
        process(HA, sorter, selector)
       
    logger.debug('Writing back CRFs.')
    tmpdir = os.path.dirname(filenames[0])
    new_filenames = [os.path.join(tmpdir, 'opt_combine_eval%d' % k) for k in xrange(common.ncpus)]
    Q = [DiskList(f) for f in new_filenames]

    idx = 0
    for cr in HA.values():
        if not cr:
            continue
        Q[idx].append(cr)
        idx = (idx + 1) % common.ncpus

    for f in filenames:
        DiskList(f).unlink()

    return new_filenames

def optimise(filenames):
    for opt in [_optimise_match, _optimise_combine]:
        filenames = opt(filenames)
    return filenames


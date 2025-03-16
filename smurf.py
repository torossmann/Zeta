"""
Operations for sums of rational functions and an interface to (a patched version of) LattE's 'count'.
"""

from sage.all import (ZZ, Compositions, SR, exp, QQ, prod, PolynomialRing,
                      vector, random_vector, matrix, FractionField)
from sage.rings.all import CommutativeRing

from . import common

from .util import my_find_executable, TemporaryDirectory, cd, augmented_env
from .cycrat import CyclotomicRationalFunction

from .tmplist import TemporaryList

import itertools

import subprocess

from .util import create_logger
logger = create_logger(__name__)

common.count = my_find_executable('count')


def NonnegativeCompositions(n, length=None):
    """
    Produce all k-lists of nonnegative integers that sum up to k.
    """
    for c in Compositions(n + length, length=length):
        yield [a - 1 for a in c]


def get_totally_nonperp_vector(vectors, strategy='random'):
    """
    Construct a vector 'w' such that w * v != 0 for all v in vectors.
    """
    vectors = list(vectors)  # We want to allow generators.

    if not vectors:
        return None

    n = len(vectors[0])
    for k in (k for k in itertools.count() for _ in range((k + 1) * n)):
        if strategy == 'random':
            v = random_vector(n, x=-k, y=k + 2)
        elif strategy == 'moment':
            v = vector(ZZ, [1] + [k ** i for i in range(1, n)])
        else:
            raise TypeError('unknown strategy')

        if 0 in (v * w for w in vectors):
            continue
        return v


def taylor_processor_naive(new_ring, Phi, scalar, alpha, I, omega):
    k = alpha.nrows() - 1
    tau = SR.var('tau')
    y = [SR('y%d' % i) for i in range(k + 1)]

    R = PolynomialRing(QQ, len(y), y)
    beta = [a * Phi for a in alpha]

    def f(i):
        if i == 0:
            return QQ(scalar) * y[0] * exp(tau * omega[0])
        elif i in I:
            return 1 / (1 - exp(tau * omega[i]))
        else:
            return 1 / (1 - y[i] * exp(tau * omega[i]))

    h = prod(f(i) for i in range(k + 1))

    # Get constant term of h as a Laurent series in tau.
    g = h.series(tau, 1).truncate().collect(tau).coefficient(tau, 0)
    g = g.factor() if g else g
    yield CyclotomicRationalFunction.from_split_expression(g, y, R).monomial_substitution(new_ring, beta)


def taylor_processor_factored(new_ring, Phi, scalar, alpha, I, omega):
    k = alpha.nrows() - 1
    tau = SR.var('tau')
    y = [SR('y%d' % i) for i in range(k + 1)]

    R = PolynomialRing(QQ, len(y), y)
    beta = [a * Phi for a in alpha]

    ell = len(I)

    def f(i):
        if i == 0:
            return QQ(scalar) * y[0] * exp(tau * omega[0])
        elif i in I:
            return tau / (1 - exp(tau * omega[i]))
        else:
            return 1 / (1 - y[i] * exp(tau * omega[i]))

    H = [f(i).series(tau, ell + 1).truncate().collect(tau) for i in range(k + 1)]

    for i in range(k + 1):
        H[i] = [H[i].coefficient(tau, j) for j in range(ell + 1)]

    r = []

    # Get coefficient of tau^ell in prod(H)

    for w in NonnegativeCompositions(ell, k + 1):
        r = prod(
            CyclotomicRationalFunction.from_split_expression(H[i][w[i]], y, R).monomial_substitution(new_ring, beta)
            for i in range(k + 1))
        yield r


def latteify_polyhedron(P):
    res = []
    lin = []

    for s in P.cdd_Hrepresentation().splitlines():
        s = s.strip()
        if s in ['H-representation', 'begin', 'end']:
            continue
        elif s.find('rational') != -1:
            res.append(s[:-len(' rational')])
        elif s.find('linearity') != -1:
            lin.append(s)
        else:
            res.append(s)
    return '\n'.join(res + lin) + '\n'


class SMURF:
    """
    Sums of MUltivariate Rational Functions.
    """

    def __init__(self, arg, base_list=None):
        # A sufficiently list-like object 'base_list' can be provided;
        # otherwise, we just use a native list.

        self.summands = [] if base_list is None else base_list
        if isinstance(arg, CommutativeRing):
            self.ring = arg
        elif isinstance(arg, CyclotomicRationalFunction):
            self.summands.append(arg.copy())
            self.ring = arg.ring
        else:  # we're expecting a non-empty iterable of CyclotomicRationalFunctions
            self.summands.extend(a.copy() for a in arg)
            self.ring = self.summands[0].ring

        if not self.__is_consistent():
            raise TypeError('These rational functions do not belong together')

    def __is_consistent(self):
        return all(self.summands[0].is_compatible_with(a)
                   for a in self.summands)

    def __iter__(self):
        return iter(self.summands)

    def __add__(self, other):
        if other == 0:
            other = SMURF(self.ring)  # this allows us to use 'sum' for SMURFs

        if (not self.summands) and (not other.summands):
            if self.ring != other.ring:
                raise TypeError('Different rings')
            return SMURF(self.ring)
        return SMURF(itertools.chain(self.summands, other.summands))

    __radd__ = __add__

    def extend(self, other):
        if self.ring != other.ring:
            raise TypeError('Different rings')

        self.summands.extend(other.summands)
        if not self.__is_consistent():
            raise TypeError

    __iadd__ = extend

    def append(self, cr):
        self.summands.append(cr)
        if not self.__is_consistent():
            raise TypeError

    def __str__(self):
        return 'Sum of %d cyclotomic rational functions over %s' % (len(self.summands), self.ring.gens())

    def evaluate(self, variables=None):
        # This is included for debugging purposes!
        return sum(SR(s.evaluate(variables)) for s in self.summands)

    def monomial_substitution(self, new_ring, Phi, base_list=None, taylor_processor=None):
        """
        Perform monomial substitutions which are valid for the sum of 'self'
        but perhaps not for each summand.
        The algorithm used can be found in Lemma 2.5 and Theorem 2.6 of
        Barvinok, Woods: ``Short rational generating functions for lattice point
        problems'', JAMS (2003).
        """

        # NOTE:
        # we only ever apply this function to sums which compute an integral.

        if taylor_processor is None:
            taylor_processor = taylor_processor_factored  # taylor_processor_naive

        if not(self.summands):
            return SMURF(new_ring, base_list=base_list)

        v = get_totally_nonperp_vector(
            vector(QQ, w) for w in itertools.chain.from_iterable(
                f.exponents[1:] for f in self.summands))

        Phi = matrix(QQ, Phi)
        L = Phi.column_space()
        Lperp = L.basis_matrix().right_kernel()

        with TemporaryList() as res:
            for f in itertools.chain.from_iterable(s.triangulate() for s in self.summands):
                # First, try to apply the substitution directly. Only if that fails,
                # do we use the far more involved method of Barvinok & Woods.
                try:
                    res.append(f.monomial_substitution(new_ring, Phi))
                    continue
                except ZeroDivisionError:
                    pass

                # Setting: f == scalar * X^alpha[0] / prod(1 - X^alpha[i], i=1..k)
                scalar, alpha, k = f.polynomial, matrix(QQ, f.exponents), len(f.exponents) - 1  # Note the final '-1'!
                if not scalar:
                    continue
                assert scalar.is_constant()  # note the use of 'triangulate' above

                omega = [v * a for a in alpha]
                I = [i for i in range(1, k + 1) if alpha[i] in Lperp]
                res.extend(taylor_processor(new_ring, Phi, scalar, alpha, I, omega))

            return SMURF(new_ring, base_list=base_list) if not res else SMURF(res, base_list=base_list)

    @classmethod
    def from_polyhedron(cls, P, ring, base_list=None):
        """
        Use LattE to compute the generating function of a rational polyhedron
        as a sum of small rational functions.
        """

        if P.is_empty():
            if ring.ngens() != P.ambient_dim():
                raise TypeError('Dimension mismatch')
            return cls(ring, base_list=base_list)
        elif P.is_zero():
            return cls([CyclotomicRationalFunction(ring.one())], base_list=base_list)
        elif len(P.vertices()) == 1 and (not P.rays()) and (not P.lines()):
            # For some reason, LattE doesn't produce .rat files for points.
            return cls([CyclotomicRationalFunction(ring.one(), exponents=[vector(ZZ, P.vertices()[0])])])

        hrep = 'polyhedron.hrep'
        ratfun = hrep + '.rat'

        with TemporaryDirectory() as tmpdir, cd(tmpdir):
            with open(hrep, 'w') as f:
                f.write(latteify_polyhedron(P))

            with open('/dev/null', 'w') as DEVNULL:
                retcode = subprocess.call([common.count,
                                           '--compute-vertex-cones=4ti2',
                                           '--triangulation=cddlib',
                                           '--multivariate-generating-function', hrep],
                                          stdout=DEVNULL, stderr=DEVNULL,
                                          env=augmented_env(common.count))
            if retcode != 0:
                raise RuntimeError('LattE failed. Make sure it has been patched in order to be compatible with Zeta.')

            K = FractionField(ring)
            variables = [K.coerce(x) for x in ring.gens()]

            def exp(a):
                return K.prod(x**e for x, e in zip(variables, a))

            def vectorise_string(s):
                return vector(ZZ, s.strip().split())

            with TemporaryList() as summands, open(ratfun, 'r') as f:
                # from functools import reduce 
                # print(reduce(lambda x, y: x + y, f.readlines(), ''))
                while True:
                    line = f.readline()
                    if not line:
                        break

                    line = line.strip()
                    if not line:
                        continue  # ignore empty lines

                    # It seems that LattE 1.7.6 does not produce the same
                    # format. Instead it seems to write the rational functions
                    # directly. The new form is 
                    # <polynomial_1>/((1 - x^a1)* ... *(1 - x^an))
                    #  + <polynomial_2>/((1 - x^b1)* ... *(1 - x^bn))
                    # ...
                    # 
                    # The variables are written like 'x[0]*x[1]', and the
                    # monomials x^ai are written out as a Laurent monomial.
                    #                                       Josh Maglione 
                    #                                       18 May 2022
                    #   
                    # # The modified version of 'count' produces files in the following format:
                    # # {
                    # # scalar
                    # # nterms
                    # # a[1] ... a[n]  \
                    # # ...            | nterms many
                    # # c[1] ... c[n]  /
                    # # nrays
                    # # u[1] ... u[n] \
                    # # ...           | nrays many
                    # # w[1] ... w[n] /
                    # # }
                    # # ...
                    # # This corresponds to scalar * sum(X^a + ... + X^c) / (1 - X^u) / ... / (1-X^w).

                    # if line != "{":
                    #     raise RuntimeError('Invalid LattE output (BEGIN) [line=%s]' % line)

                    # scalar = ring(f.readline())
                    # nterms = int(f.readline())
                    # numerator = K(scalar) * K.sum(exp(vectorise_string(f.readline())) for _ in range(nterms))

                    # nrays = int(f.readline())
                    # exponents = [vector(ZZ, len(variables))] + [vectorise_string(f.readline()) for _ in range(nrays)]
                    # line = f.readline().strip()

                    # if line != '}':
                    #     raise RuntimeError('Invalid Latte output (END)')

                    # We do some basic string manipulation, only resorting to
                    # symbolic manipulation when most convenient (for degrees).
                    rat_str = line.replace('[', '').replace(']', '')
                    num_str, den_str = rat_str.split('/')
                    factors_str = den_str.split('*(')
                    exponents = [vector(ZZ, len(variables))]
                    for fact in factors_str:
                        if ")^" in fact:
                            i = fact.index(")^")
                            f_exp = int(fact[i+2:])
                            lpoly = SR(fact[:i].replace(')', '').replace('(', '')) 
                        else:
                            f_exp = 1
                            lpoly = SR(fact.replace(')', '').replace('(', ''))
                        lmono = -lpoly + 1 # Assuming form 1 - X^a
                        v = vector(ZZ, [lmono.degree(x) for x in ring.gens()])
                        for _ in range(f_exp):
                            exponents.append(v) 
                    numerator = K(num_str)

                    summands.append(CyclotomicRationalFunction.from_laurent_polynomial(numerator, ring, exponents))

                return cls(summands, base_list=base_list)

"""Utility functions that don't belong anywhere else.
"""

from sage.all import *
from itertools import chain
from distutils.spawn import find_executable
from pkg_resources import resource_exists, resource_filename

import logging
handler = logging.StreamHandler()
handler.setLevel(logging.DEBUG)

def create_logger(name, level=logging.WARNING):
    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.propagate = False
    if not logger.handlers:
        handler.setFormatter(logging.Formatter('%(asctime)s %(name)s %(levelname)s - %(message)s', '%Y-%m-%d %H:%M:%S'))
        logger.addHandler(handler)
    return logger

logger = create_logger(__name__)

# Decorator for functions taking a single argument 'self'.
# After the first call, the cached result is stored as an
# attribute of 'self'.

def cached_simple_method(f, name=None):
    if name is None:
        name = '_cached_' + f.__name__

    def cached_f(self):
        try:
            return getattr(self, name)
        except AttributeError:
            res = f(self)
            setattr(self, name, res)
            return res
    return cached_f

def monomial_log(g):
    if not (g.is_constant() or g.is_monomial()):
        raise ValueError('Can only take logs of monomials')
    if g.denominator() == Integer(1):
        return vector(g.numerator().exponents()[0])
    else:
        return vector(g.numerator().exponents()[0]) - vector(g.denominator().exponents()[0])

def monomial_exp(R, v):
    return prod(map(lambda w: w[0]**w[1], zip(R.gens(),list(v))))

def E(n, i, j, ring=QQ):
    A = Matrix(ring, n)
    A[i,j] = 1
    return A

def unzip(li):
    return tuple(zip(*li))

def normalise_poly(f):
    return f/f.lc()

def initial_form_by_direction(f, y):
    """Determine the initial form of 'f' in direction 'y'.
    """

    mon, coeff = f.monomials(), f.coefficients()
    weights = [monomial_log(m)*y for m in mon]
    w = min(weights)
    return sum(coeff[k]*mon[k] for k in xrange(len(mon)) if weights[k] == w)

def is_subpolynomial(f, a):
    """Test if `a' is a sum of terms of the polynomial `f'.
    """
    a = f.parent()(a)
    return len(f.monomials()) == len((f-a).monomials()) + len(a.monomials())

def subpolynomial_meet(f,g):
    """Find the 'largest' common subpolynomial of 'f' and 'g'.
    """
    mon_f, coeff_f = f.monomials(), f.coefficients()
    mon_g, coeff_g = g.monomials(), g.coefficients()

    r = f.parent()(0)
    for i in xrange(len(mon_f)):
        if mon_f[i] in mon_g:
            k = mon_g.index(mon_f[i])
            if coeff_f[i] == coeff_g[k]:
                r += coeff_f[i] * mon_f[i]
    return r

def normalise_laurent_polynomial(f):
    """
    Rescale a Laurent polynomial by Laurent monomials. Details TBA.
    """

    # Since Sage's Laurent polynomials are useless, we just use rational
    # functions instead.
    # First make sure, 'f' really is one.

    R = f.parent()
    K = FractionField(R)
    f = K(f)
    if K.ngens() == 0:
        return R(0) if not f else R(1)

    f = f.numerator()
    return R(f / gcd(f.monomials()))

def terms_of_polynomial(f):
    return [c*t for c,t in zip(f.coefficients(), f.monomials())]

import contextlib, shutil, tempfile

@contextlib.contextmanager
def TemporaryDirectory(delete=True):
    name = tempfile.mkdtemp()
    try:
        yield name
    finally:
        if delete:
            shutil.rmtree(name)

@contextlib.contextmanager
def cd(dir):
    oldcwd = os.getcwd()
    try:
        yield
    finally:
        os.chdir(oldcwd)

def readable_filesize(size):
    return '%.1f %s' % ((size/1024.0, 'KB') if size <= 512*1024
                        else ( (size/1024.0/1024.0, 'MB'))
                        if size <= 512*1024*1024 else (size/1024.0/1024.0/1024.0, 'GB'))
              
def my_find_executable(name):
    foo = find_executable(name)
    if foo:
        return os.path.abspath(foo)
    try:
        if resource_exists('Zeta', name):
            return resource_filename('Zeta', name)
    except:
        return None

def minimal_elements(P, lte):
    # Let (P,lte) be a preordered set. Find a set of representatives
    # of the minimal elements in the quotient poset.

    P = list(P)
    active = range(len(P))
    for i in xrange(len(P)):
        if i not in active:
            continue
        for j in active[:]:
            if i == j:
                continue
            if lte(P[i], P[j]):
                active.remove(j)
    return [P[i] for i in active]

def squarefree_part(f):
    if not f:
        return f
    R = f.parent()
    return R(prod(h for h,_ in f.factor()))

def split_off_torus(F):
    # Given a list F of polynomials, return G,d,T where len(F) == len(G)
    # and G consists of polynomials in d variables; T = change of basis.
    # There exists A in GL(n,ZZ) s.t. F[i]^A == G[i] * (Laurent term).
    # In particular, F is non-degenerate relative to {0} iff this the case
    # for G; cf Remark 4.3(ii) and Lemma 6.1(ii) in arXiv:1405.5711.
    #
    # The number of variables in G is the dimension of Newton(prod(F)).
    #

    if not F:
        return [], 0, None

    R = F[0].parent()
    v = {f:vector(ZZ,f.exponents()[0]) for f in F}
    submodule = (ZZ**R.ngens()).submodule(chain.from_iterable((vector(ZZ,e)-v[f] for e in f.exponents()) for f in F))
    _,_,T = matrix(ZZ, submodule.basis_matrix()).smith_form()
    d = submodule.rank()
    Rd = PolynomialRing(QQ, d, R.gens()[:d])
    K = FractionField(R)
    return [Rd(normalise_laurent_polynomial(K(f([monomial_exp(K,e) for e in T.rows()])))) for f in F], d, T

def principal_minors(A, size):
    m = A.nrows()
    n = A.ncols()
    r = min(m, n)
    li = []
    for idx in Subsets(range(r), size):
        idx = list(idx)
        li.append(A.base_ring()(A.matrix_from_rows_and_columns(idx, idx).determinant()))
    return li

def MyCompositions(n,length):
    if n < length or not length:
        return
    if length==1:
        yield [n]
        return

    for i in xrange(1, n-length+2):
        for c in MyCompositions(n-i, length-1):
            yield [i] + c

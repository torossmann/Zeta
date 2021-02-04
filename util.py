"""Utility functions that don't belong anywhere else.
"""

from sage.all import *
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

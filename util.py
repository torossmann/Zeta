"""Utility functions that don't belong anywhere else.
"""

from sage.all import Integer, vector, prod, QQ, Matrix, FractionField, gcd, ZZ, matrix, PolynomialRing, Subsets, SR, lcm, identity_matrix
from itertools import chain
from distutils.spawn import find_executable
from pkg_resources import resource_exists, resource_filename

import os
import contextlib
import shutil
import tempfile

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
    return prod(map(lambda w: w[0]**w[1], zip(R.gens(), list(v))))


def split_vector(v):
    vpos = vector(x if x > Integer(0) else Integer(0) for x in v)
    vneg = vector(-x if x < Integer(0) else Integer(0) for x in v)
    return (vpos, vneg)


def E(n, i, j, ring=QQ):
    A = Matrix(ring, n)
    A[i, j] = 1
    return A


def unzip(li):
    return tuple(zip(*li))


def normalise_poly(f):
    return f / f.lc()


def initial_form_by_direction(f, y):
    """Determine the initial form of 'f' in direction 'y'.
    """

    mon, coeff = f.monomials(), f.coefficients()
    weights = [monomial_log(m) * y for m in mon]
    w = min(weights)
    return sum(coeff[k] * mon[k] for k in range(len(mon)) if weights[k] == w)


def vertex_by_direction(polytope, y):
    """Return one(!) vertex on the face of 'polytope' defined by
    minimising 'y'.
    """
    if polytope.is_empty():
        raise ValueError('need a non-empty polytope')
    vertices = polytope.vertices_matrix().transpose()
    w = min(x * y for x in vertices)
    return next(x for x in vertices if x * y == w)


def is_subpolynomial(f, a):
    """Test if `a' is a sum of terms of the polynomial `f'.
    """
    a = f.parent()(a)
    return len(f.monomials()) == len((f - a).monomials()) + len(a.monomials())


def subpolynomial_meet(f, g):
    """Find the 'largest' common subpolynomial of 'f' and 'g'.
    """
    mon_f, coeff_f = f.monomials(), f.coefficients()
    mon_g, coeff_g = g.monomials(), g.coefficients()

    r = f.parent()(0)
    for i in range(len(mon_f)):
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
    return [c * t for c, t in zip(f.coefficients(), f.monomials())]


def evaluate_polynomial(f, v):
    if not f:
        return f.parent().zero()

    def exp(e):
        return prod(x**e for x, e in zip(v, e))
    return sum(scalar * exp(e) for scalar, e in zip(f.coefficients(), f.exponents()))


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
        os.chdir(dir)
        yield
    finally:
        os.chdir(oldcwd)


def readable_filesize(size):
    return '%.1f %s' % ((size / 1024.0, 'KB') if size <= 512 * 1024
                        else ((size / 1024.0 / 1024.0, 'MB'))
                        if size <= 512 * 1024 * 1024 else (size / 1024.0 / 1024.0 / 1024.0, 'GB'))


def my_find_executable(name):
    s = os.path.join('bin', name)
    try:
        if resource_exists('Zeta', s):
            return os.path.abspath(resource_filename('Zeta', s))
    except:
        pass

    filename = find_executable(name)
    return os.path.abspath(filename) if filename else None


def minimal_elements(P, lte):
    # Let (P,lte) be a preordered set. Find a set of representatives
    # of the minimal elements in the quotient poset.

    P = list(P)
    active = list(range(len(P)))
    for i in range(len(P)):
        if i not in active:
            continue
        for j in active[:]:
            if i == j:
                continue
            if lte(P[i], P[j]):
                active.remove(j)
    return [P[i] for i in active]


def squarefree_part(f):
    # NOTE: f.factor().unit() is discarded
    return f.parent().prod(h for h, _ in f.factor()) if f else f


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
    v = {f: vector(ZZ, f.exponents()[0]) for f in F}
    submodule = (ZZ**R.ngens()).submodule(chain.from_iterable((vector(ZZ, e) - v[f] for e in f.exponents()) for f in F))
    _, _, T = matrix(ZZ, submodule.basis_matrix()).smith_form()
    d = submodule.rank()
    Rd = PolynomialRing(QQ, d, R.gens()[:d])
    K = FractionField(R)
    return [Rd(normalise_laurent_polynomial(K(f([monomial_exp(K, e)
                                                 for e in T.rows()]))))
            for f in F], d, T


def principal_minors(A, size):
    m = A.nrows()
    n = A.ncols()
    r = min(m, n)
    li = []
    for idx in Subsets(range(r), size):
        idx = list(idx)
        li.append(A.base_ring()(A.matrix_from_rows_and_columns(idx, idx).determinant()))
    return li


def upper_triangular_matrix(R, d, entries):
    entries = iter(entries)
    M = matrix(R, d, d)
    for i in range(d):
        for j in range(i, d):
            M[i, j] = next(entries)
    return M


def MyCompositions(n, length):
    if n < length or not length:
        return
    if length == 1:
        yield [n]
        return

    for i in range(1, n - length + 2):
        for c in MyCompositions(n - i, length - 1):
            yield [i] + c


def common_overring(R, S):
    if R.has_coerce_map_from(S):
        return R
    elif S.has_coerce_map_from(R):
        return S
    else:
        combined_vars = list(set(R.base_ring().gens()) | set(S.base_ring().gens()))
        K = FractionField(PolynomialRing(QQ, len(combined_vars), combined_vars))
        return PolynomialRing(K, R.gens())


def is_block_diagonal_matrix(A, blocks):
    if not A.is_square():
        raise ValueError

    partial_sums = [sum(blocks[:i]) for i in range(len(blocks) + 1)]
    n = A.nrows()
    if partial_sums[-1] != n:
        raise ValueError

    for r in range(len(partial_sums) - 1):
        a = partial_sums[r]
        b = partial_sums[r + 1]

        for i in range(a, b):
            for j in range(b, n):
                if A[i, j] != 0 or A[j, i] != 0:
                    return False
    return True


def symbolic_to_polynomial(f, vars):
    # Rewrite a symbolic expression as a polynomial over SR in a given
    # list of variables.

    poly = f.polynomial(QQ)
    allvars = poly.variables()

    indices = []
    for x in allvars:
        try:
            indices.append(vars.index(x))
        except ValueError:
            indices.append(None)

    R = PolynomialRing(SR, len(vars), vars)
    res = R.zero()
    for coeff, alpha in zip(poly.coefficients(), poly.exponents()):
        if type(alpha) == int:
            # Once again, univariate polynomials receive special treatment
            # in Sage.
            alpha = [alpha]

        term = R(coeff)
        for i, e in enumerate(alpha):
            if not e:
                continue
            if indices[i] is None:
                term *= SR(allvars[i]**e)
            else:
                term *= R.gen(indices[i])**e
        res += term
    return res


def symbolic_to_ratfun(f, vars):
    R = PolynomialRing(QQ, len(vars), vars)
    try:
        return R(f.numerator()) / R(f.denominator()), R
    except TypeError:
        pass

    num = symbolic_to_polynomial(f.numerator(), vars)
    den = symbolic_to_polynomial(f.denominator(), vars)
    return num / den, num.parent()


def augmented_env(filename):
    env = os.environ.copy()
    env['PATH'] = os.path.dirname(filename) + os.path.pathsep + env.get('PATH', '')
    return env


def evaluate_matrix(A, y, ring=None):
    if ring is None:
        ring = y[0].parent()
    return matrix(ring, [[entry(list(y)) for entry in rows] for rows in A])


def basis_of_matrix_algebra(gens, product=None):
    """
    Given a list of rational square matrices, compute
    a basis of the rational matrix algebra they generate.
    """
    if (product is None) or (product == 'zero'):
        mult = lambda a, b: 0 * a
    elif product == 'associative':
        mult = lambda a, b: a * b
    elif product == 'Lie':
        mult = lambda a, b: a * b - b * a
    else:
        mult = product

    if not gens:
        return []

    n = gens[0].nrows()
    V = QQ**(n**2)
    U = V.subspace([g.list() for g in gens])

    while True:
        W = U
        for b in U.basis():
            for c in U.basis():
                v = vector(mult(Matrix(QQ, n, n, list(b)),
                                Matrix(QQ, n, n, list(c))).list())
                if v not in W:
                    W = W + V.subspace([v])
        if W == U:
            break
        else:
            U = W

    def normalise(w):
        c = lcm([a.denominator() for a in w])
        return [ZZ(c * a) for a in w]
    return [Matrix(QQ, n, n, normalise(list(b))) for b in U.basis()]


def matlist_to_mat(mats, n=None):
    if not mats and n is None:
        raise ValueError('cannot guess size of matrices')
    R = PolynomialRing(QQ, 'y', len(mats))
    if not mats:
        return matrix(R, n, n)
    return matrix(R, sum(R.gen(i) * a for i, a in enumerate(mats)))


def mat_to_matlist(A):
    return [matrix(QQ, [[a(list(e)) for a in rows] for rows in A])
            for e in identity_matrix(QQ, A.base_ring().ngens())]


def subspace_structured_basis(U, V):
    """Let U and V be subspaces of some common vector space W.
    Construct a basis matrix of W which contains bases of U, V, and U cap V as
    subsets with specified indices. The coordinates outside of U+V will be
    last."""

    if U.ambient_vector_space() != V.ambient_vector_space():
        raise ValueError

    ################################################
    # Picture
    ################################################
    #   R^n
    #    |
    #    |   A[3]
    #    |
    #   U+V == S
    #    |
    #    |   A[2]
    #    |
    #    U
    #    |
    #    |   A[1]
    #    |
    # U cap V == I
    #    |
    #    |   A[0]
    #    |
    #    0

    S = U + V
    I = U.intersection(V)
    C = I.complement()

    A = [I, U.intersection(C), V.intersection(C), S.complement()]
    indices_U = list(range(U.dimension()))
    indices_V = (list(range(I.dimension())) +
                 list(range(U.dimension(), U.dimension() + A[2].dimension())))
    indices_U_cap_V = list(range(I.dimension()))
    rem = U.dimension() + A[2].dimension()
    indices_remaining = list(range(rem, rem + A[3].dimension()))

    return (Matrix(U.base_ring(), [x for a in A for x in a.basis()]),
        [indices_U, indices_V, indices_U_cap_V, indices_remaining])


def graph_to_generic_matrix(G, t):
    if t not in ['symmetric', 'antisymmetric']:
        raise ValueError('unsupported type of matrix')
    if G.has_multiple_edges():
        raise ValueError('parallel edges not supported')

    A = G.adjacency_matrix()
    d = A.nrows()
    n = sum(A[i, j] for i in range(d) for j in range(i, d))
    R = PolynomialRing(QQ, n, 'x')
    B = matrix(R, d, d)

    it = iter(R.gens())

    for i in range(d):
        for j in range(i, d):
            B[i, j] = next(it) if A[i, j] else 0
            if i < j:
                B[j, i] = -B[i, j] if t == 'antisymmetric' else B[i, j]
    return B


def is_matrix(A):
    try:
        A.matrix_space
        return True
    except AttributeError:
        return False


def is_polynomial(f):
    try:
        f.content_ideal
        return True
    except AttributeError:
        return False


def is_list(L):
    try:
        L.append
        return True
    except AttributeError:
        return False


def is_graph(G):
    try:
        G.num_verts
        return True
    except AttributeError:
        return False


def is_string(s):
    try:
        s.capitalize
        return True
    except AttributeError:
        return False

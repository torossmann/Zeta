"""
Some specialised functionality for cones, polyhedra, and polytopes.
"""

from sage.all import *
from sage.geometry.cone import ConvexRationalPolyhedralCone

import itertools
from collections import Iterable

from util import monomial_exp, cached_simple_method

import triangulate

def conify_polyhedron(P):
    """Compute the cone spanned by a polyhedron.
    """
    if isinstance(P, ConvexRationalPolyhedralCone):
        return P
    else:
        V = [vector(QQ,v) for v in P.vertices()]
        R = [vector(QQ,v) for v in P.rays()]
        Lplus = [vector(QQ,v) for v in P.lines()]
        Lminus = [-v for v in Lplus]
        return Cone(V+R+Lplus+Lminus, lattice=ZZ**P.ambient_dim())
    

def is_contained_in_dual(C, D):
    """Test if the cone C is contained in the dual of the cone D.
    """
    for v,w in itertools.product(C.rays(), D.rays()):
        if vector(QQ, v) * vector(QQ, w) < Rational(0):
            return False
    return True


def dual_cone_as_polyhedron(rays, strict=False):
    """Compute the polyhedron consisting of all y such that
    r * y >= 0 (or r * y > 0 if strict=True) for r in rays.
    """
    if len(rays) == 0:
        raise TypeError('Need at least one ray')
    c = Integer(-1) if strict else Integer(0)
    return Polyhedron(ieqs=[[c] + list(v) for v in rays], base_ring=QQ)

def inner_open_normal_fan(N):
    """
    Construct the relatively open, inner normal fan of a lattice
    polytope.

    We approximate 'x > 0' via 'x >= 1', see the part on 'models' of half-open
    cones in the second paper.
    """
    V = [vector(QQ,v) for v in N.vertices()]

    for face in N.face_lattice():
        if face.dim() == -1:
            continue
        W = [vector(QQ,w) for w in face.vertices()]

        eqns = [vector(QQ, [0] + list(W[0] - W[i])) for i in xrange(1,len(W))]
        idx = [i for i in xrange(len(V)) if not(V[i] in W)]
        ieqs = [vector(QQ, [-1] + list(V[i] - W[0])) for i in idx]
        yield Polyhedron(ieqs=ieqs, eqns=eqns)

    # This function will be called a lot so we cannot afford to cache
    # return values.
    N.face_lattice.clear_cache()

def linear_image_of_polyhedron(P, A):
    if A.nrows() != P.ambient_dim():
        raise ValueError('matrix does not act on ambient space of polyhedra')
    return Polyhedron(ambient_dim=P.ambient_dim(),
                      vertices=[vector(v)*A for v in P.vertices()],
                      rays=[vector(r)*A for r in P.rays()],
                      lines=[vector(l)*A for l in P.lines()])
    
def get_point_in_polyhedron(P):
    if len(P.vertices()) == 0:
        raise TypeError('What a strange polyhedron you gave me')
    return vector(QQ, P.vertices()[0])

def PositiveOrthant(d):
    if d == 0:
        return Polyhedron(ambient_dim=0,eqns=[],ieqs=[(0,)], base_ring=QQ)
    else:
        return Polyhedron(ieqs=block_matrix([[matrix(QQ,d,1),identity_matrix(QQ,d)]]))

def StrictlyPositiveOrthant(d):
    if d == 0:
        return Polyhedron(ambient_dim=0, vertices=[()], base_ring=QQ)
    else:
        return Polyhedron(ieqs=block_matrix([[matrix(QQ,d,1,[-1 for i in xrange(d)]),identity_matrix(QQ,d)]]))

def _mixed_volume_naive(gen):
    """
    Naive computation of the normalised mixed volume using Cox et al.,
    'Using Algebraic Geometry', Thm 7.4.12.
    """

    P = list(gen)
    n = len(P)

    if any(q.ambient_dim() != n for q in P):
        raise TypeError('Number of polytopes and ambient dimension do not match')
    res = 0
    for I in Subsets(range(n)):
        if not I:
            continue
        res += (-1)**len(I) * (sum(P[i] for i in I)).volume()

    return (-1)**n/Integer(factorial(n)) * res

def _mixed_volume_gfan(gen):
    """
    Use gfan to compute the mixed volume of a collection of polytopes.
    Just like Khovanskii, we use the normalised mixed volume which satisfies
    mixed_volume([P,...,P]) = volume(P).
    """

    P = list(gen)
    n = len(P)

    if any(Q.ambient_dim() != n for Q in P):
        raise TypeError('Number of polytopes and ambient dimension do not match')

    if n == 0:
        return 0
    elif n == 1:
        return P[0].volume()

    R = PolynomialRing(QQ, 'x', n)
    I = R.ideal([ sum(monomial_exp(R,e) for e in Q.vertices()) for Q in P ])
    return Integer(1)/Integer(factorial(n)) * I.groebner_fan().mixed_volume()

mixed_volume = _mixed_volume_gfan

def DirectProductOfPolyhedra(P, Q):
    m = P.ambient_dim()
    n = Q.ambient_dim()

    ieqs = []
    eqns = [(n+m+1)*(0,)] # ensures correctness when P == RR^m, Q==RR^n

    # [b | a] --> [b | a | 0]
    f = lambda v: v + n * [0]

    # [b | a] --> [b | 0 | a]
    g = lambda v: [v[0]] + m * [0] + v[1:]

    for i in P.inequalities():
        ieqs.append(f(list(i)))
    for i in Q.inequalities():
        ieqs.append(g(list(i)))

    for e in P.equations():
        eqns.append(f(list(e)))
    for e in Q.equations():
        eqns.append(g(list(e)))
    return Polyhedron(ieqs=ieqs, eqns=eqns, base_ring=QQ, ambient_dim=m+n)

class RationalSet:
    # Disjoint(!) unions of rational polyhedra.
    def __init__(self, arg, ambient_dim=None, check=False):
        try:
            polyhedra = list(Set(arg))
        except TypeError:
            polyhedra = [arg]

        if not polyhedra:
            if ambient_dim is None:
                raise ValueError('need to specify ambient dimension')
            self.ambient_dim = ambient_dim
            self.polyhedra = []
            self.cones = []
            return

        self.ambient_dim = polyhedra[0].ambient_dim() if ambient_dim is None else ambient_dim
        polyhedra = [P for P in polyhedra if not P.is_empty()]
        self.polyhedra = polyhedra
        self.cones = [conify_polyhedron(P) for P in polyhedra]

        if any(P.ambient_dim() != self.ambient_dim for P in polyhedra):
            raise ValueError('inconsistent ambient dimensions')

        if check and any(not (P & Q).is_empty() for P,Q in itertools.combinations(polyhedra, 2)):
            raise ValueError('polyhedra are not disjoint')

    def triangulate_max(self, dims=None):
        # Return a triangulation of the maximal-dimensional parts (or all
        # parts of specified dimensions) only.
        if dims is None:
            dims = [self.dim()]
        for C in self.cones:
            if C.dim() not in dims:
                continue
            if C.dim() == 0:
                raise RuntimError("what's a triangulation of the trivial cone?")
            for scone in triangulate.triangulate_cone(C):
                yield scone
    
    def topologise(self, Phi, dims=None):
        if self.dim() == 0:
            # NOTE: For the cone {0}, the generating function is just 1;
            # hence, Phi doesn't matter.
            yield triangulate.SURF(scalar=1, rays=[])
            return

        for scone in self.triangulate_max(dims=dims):
            yield triangulate._topologise_scone(scone, Phi)
            
    def is_empty(self):
        return not self.polyhedra

    @cached_simple_method
    def dim(self):
        return -1 if not self.polyhedra else max(P.dim() for P in self.polyhedra)

    def intersection(self, other):
        if self.ambient_dim != other.ambient_dim:
            raise ValueError('ambient dimensions differ')
        return RationalSet([P & Q for P,Q in itertools.product(self.polyhedra, other.polyhedra)],
                           ambient_dim=self.ambient_dim)
    __and__ = intersection

    def __mul__(self, other):
        return RationalSet([DirectProductOfPolyhedra(P,Q) for P,Q in itertools.product(self.polyhedra, other.polyhedra)], ambient_dim=self.ambient_dim+other.ambient_dim)

    def dual_cone(self):
        return reduce(lambda C,D: C.intersection(D), (Cone(C.rays()).dual() for C in self.cones)) if self.cones else Cone(Polyhedron(ieqs=[(self.ambient_dim+1)*(0,)]))

    def is_contained_in_dual(self, alpha):
        return all(alpha*beta >= 0 for C in self.cones for beta in C.rays())
    
    def is_perpendicular(self, alpha):
        return all(alpha*beta == 0 for C in self.cones for beta in C.rays())

    def __repr__(self):
        s = 'Rational set consisting of %d polyhedra in RR^%d:\n' % (len(self.polyhedra), self.ambient_dim)
        for i, P in enumerate(self.polyhedra):
            s += '[%d]:\n\tdim = %d\n\t' % (i, P.dim())
            s += '\n\t'.join(str(h) for h in P.Hrep_generator()) + '\n'
        return s

def vertex_minimiser(P):
    # Decompose the ambient space into half-open cones C such that min<P,-> = <alpha,-> on each C.
    # Yields C, alpha.
    if P.is_empty():
        raise ValueError('need a non-empty polytope')

    A = P.vertices_matrix().transpose()
    n = P.ambient_dim()
    for i, alpha in enumerate(A):
        ieqs = [ [ 0] + list(A[j]-alpha) for j in xrange(i+1,A.nrows()) ]
        ieqs +=[ [-1] + list(A[j]-alpha) for j in xrange(i) ]
        ieqs +=[ [0] * (n+1)] # Needed if P is a point.
        yield Polyhedron(ieqs=ieqs, ambient_dim=n), alpha

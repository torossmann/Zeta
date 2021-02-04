from sage.all import *

import abstract
from abstract import ZetaDatum, TopologicalZetaProcessor, ReductionError

from toric import ToricDatum

from torus import SubvarietyOfTorus
from convex import conify_polyhedron, DirectProductOfPolyhedra, StrictlyPositiveOrthant
from triangulate import topologise_cone
from surf import SURF
from util import normalise_poly, terms_of_polynomial

import itertools

from util import create_logger
logger = create_logger(__name__)

BALANCE_FULL_BOUND = 10
DEPTH_BOUND = 24

class Breakout(Exception):
    pass

def null_chopper(T, indices):
    raise ReductionError('The null chopper never works')

def equality_chopper(T, indices, depth_bound=None):
    # Only decompose the polyhedron, let simplify() take care of the polynomials.
    # We discard empty stuff so calling this function multiple times does no
    # harm.

    if depth_bound is None:
        depth_bound = DEPTH_BOUND

    if T._depth > depth_bound:
        raise ReductionError('Bound for the depth exceeded. Equality chopper failed.')

    lhs = T.lhs
    rhs = T.initials if T.is_balanced() else T.rhs

    for i,j in itertools.combinations(indices,2):
        f = normalise_poly(rhs[i] * lhs[j])
        g = normalise_poly(rhs[j] * lhs[i])
        q = f/g
        if (f == g) or (normalise_poly(q.numerator()).is_monomial() and
                        normalise_poly(q.denominator()).is_monomial()):
            logger.debug('Reduction using the pair (%d,%d)' % (i,j))
            lt, rt = [T.reduce(i,j).simplify(), T.reduce(j,i,strict=True).simplify()]
            lt._depth += 1 ; rt._depth += 1
            logger.info('Left depth increased to %d' % lt._depth)
            logger.info('Right depth increased to %d' % rt._depth)
            return [lt, rt]
    raise ReductionError('Equality chopper failed')

def greedy_chopper(T, indices, depth_bound=None, use_first_improvement=False):
    if depth_bound is None:
        depth_bound = DEPTH_BOUND

    if not T.is_balanced():
        raise ReductionError('Can only handle balanced toric data')

    if len(T._coll_idx) == 1:
         raise ReductionError('Toric singularities!')

    # To ensure termination, we bound the depth of reduction steps
    # that don't lead to immediate improvements.

    inweight = lambda T: sum(len(r.monomials())-1 for r in T.initials)

    def cand(i,j,ti,tj):
        # Assigns a `badness' value between 0.0 and Infinity to a possible
        # reduction step.

        Ti = T.reduce(i,j,ti,tj).simplify()
        Tj = T.reduce(j,i,tj,ti,strict=True).simplify()

        children = [t.simplify() for t in itertools.chain(Ti.balance(), Tj.balance())]
        naughty = []
        for t in children:
            if t.is_regular():
                continue
            if inweight(t) >= inweight(T):
                t._depth += 1
                logger.info('Depth increased to %d' % t._depth)
                naughty.append(t)

        if not naughty:
            return float(0), children

        if any(t._depth > depth_bound for t in naughty):
            logger.info('Exceeded the given bound for the depth of reductions.')
            return Infinity, children

        return (float(sum(inweight(t) for t in naughty))/ (inweight(T) * len(naughty)),
                naughty + [c for c in children if c not in naughty])

    # NOTE: the partition of the polyhedron is the same for any choice of (i,j)
    # so it would suffice to compute it once for every pair (i,j).

    optval, optsol, reduction_quad = Infinity, None, None
    try:
        for i,j in itertools.combinations(indices, 2):
            for ti,tj in itertools.product(terms_of_polynomial(T.initials[i]),
                                           terms_of_polynomial(T.initials[j])):
                val, sol = cand(i,j,ti,tj)
                if val < optval:
                    optval, optsol = val, sol
                    reduction_quad = (i,j,ti,tj)
                if not optval or (use_first_improvement and optval < 1.0):
                    raise Breakout()
    except Breakout:
        pass
    if optsol is None:
        raise ReductionError('Greedy chopper failed')
    logger.info('Greedy chopper: badness after reduction %.2f' % optval)
    logger.debug('Greedy chopper: reduction candidate used is (%d, %d, %s, %s)' % (i,j,ti,tj))
    return optsol

class ReductionStrategy:
    def __init__(self, name, chopper, prechopper, order):
        self.name = name
        self.chopper = chopper
        self.prechopper = prechopper
        self.order = order

    def __str__(self):
        return 'ReductionStrategy:%s' % self.name

class Strategy:
    NORMAL = ReductionStrategy('normal', greedy_chopper, null_chopper, False)
    ORDER = ReductionStrategy('order', greedy_chopper, null_chopper, True)
    PREEMPTIVE = ReductionStrategy('preemptive', greedy_chopper, equality_chopper, True)
    NONE = ReductionStrategy('none', null_chopper, null_chopper, False)

class SubobjectDatum(ZetaDatum):
    # Just a thin wrapper on top of ToricDatum from Zeta 0.1.
    def __init__(self, T, strategy=None):
        self.toric_datum = T
        self.strategy = Strategy.NORMAL if strategy is None else strategy

    def is_empty(self):
        return self.toric_datum.is_empty()

    def simplify(self):
        return SubobjectDatum(self.toric_datum.simplify(), strategy=self.strategy)

    def is_balanced(self):
        return self.toric_datum.is_balanced()
    
    def balance(self):
        balancing_strategy = 'full' if self.toric_datum.weight() < BALANCE_FULL_BOUND else 'min'
        for B in self.toric_datum.balance(strategy=balancing_strategy):
            yield SubobjectDatum(B, strategy=self.strategy)

    def is_ordered(self):
        return (not self.strategy.order) or self.toric_datum.is_ordered()

    def order(self):
        for O in self.toric_datum.order():
            yield SubobjectDatum(O, strategy=self.strategy)

    def is_regular(self):
        return self.toric_datum.is_regular()

    def __repr__(self):
        return str(self.toric_datum)

    def reduce(self, preemptive=False):
        chops = self.strategy.prechopper(self.toric_datum, range(len(self.toric_datum.rhs))) if preemptive else self.strategy.chopper(self.toric_datum, self.toric_datum._coll_idx)
        for C in chops:
            yield SubobjectDatum(C, strategy=self.strategy)
            
class SubobjectZetaProcessor(TopologicalZetaProcessor):
    def __init__(self, algebra, objects, strategy=None):
        self.algebra = algebra
        self.objects = objects
        self.strategy = strategy
        self._root = None

    def root(self):
        if self._root is None:
            self._root = SubobjectDatum(self.algebra.toric_datum(self.objects), strategy=self.strategy)
        return self._root

    def optimise(self):
        A = self.algebra.find_good_basis(self.objects)
        self.algebra = self.algebra.change_basis(A)
        self._root = None

    def topologically_evaluate_regular(self, datum):
        T = datum.toric_datum
        if not T.is_regular():
            raise ValueError('Can only processed regular toric data')

        # All our polyhedra all really half-open cones (with a - 1 >=0
        # being an imitation of a >= 0).

        C = conify_polyhedron(T.polyhedron)

        M = Set(range(T.length()))

        logger.debug('Dimension of polyhedron: %d' % T.polyhedron.dim())

        # STEP 1:
        # Compute the Euler characteristcs of the subvarieties of
        # Torus^sth defined by some subsets of T.initials.
        # Afterwards, we'll combine those into Denef-style Euler characteristics
        # via inclusion-exclusion.

        logger.debug('STEP 1')
        s = SR.var('s')

        alpha = {} 
        tdim = {}

        for I in Subsets(M):
            logger.debug('Processing I = %s' % I)
            F = [T.initials[i] for i in I]

            V = SubvarietyOfTorus(F, torus_dim=T.ambient_dim)
            U,W = V.split_off_torus()

            # Keep track of the dimension of the torus factor for F == 0.
            tdim[I] = W.torus_dim

            if tdim[I] > C.dim():
                # In this case, we will never need alpha[I].
                logger.debug('Totally irrelevant intersection.')
                # alpha[I] = ZZ(0)
            else:
                # To ensure that the computation of Euler characteristics succeeds in case
                # of global non-degeneracy, we test this first.
                # The 'euler_characteristic' method may change generating sets,
                # possibly introducing degeneracies.
                alpha[I] = U.khovanskii_characteristic() if U.is_nondegenerate() else U.euler_characteristic()
                logger.debug('Essential Euler characteristic alpha[%s] = %d; dimension of torus factor = %d' % (I,alpha[I], tdim[I]))

        logger.debug('Done computing essential Euler characteristics of intersections: %s' % alpha)

        # STEP 2:
        # Compute the topological zeta functions of the extended cones.
        # That is, add extra variables, add variable constraints (here: just >= 0),
        # and add newly monomialised conditions.

        Z = {}

        def cat(u,v):
            return vector(list(u) + list(v))

        logger.debug('STEP 2')
        for I in Subsets(M):
            logger.debug('Current set: I = %s' % I)

            # P = C_0 x R_(>0)^I in the paper
            P = DirectProductOfPolyhedra(T.polyhedron, StrictlyPositiveOrthant(len(I)))

            it = iter(identity_matrix(ZZ, len(I)).rows())
            ieqs = []
            for i in M:
                # Turn lhs[i] | monomial of initials[i] * y[i] if in I,
                #      lhs[i] | monomial of initials[i] otherwise
                # into honest cone conditions.
                ieqs.append(
                    cat(vector(ZZ,(0,)),
                        cat(
                            vector(ZZ, T.initials[i].exponents()[0]) -
                            vector(ZZ, T.lhs[i].exponents()[0]),
                            next(it) if i in I else zero_vector(ZZ,len(I))
                            )
                        )
                    )

            if not ieqs:
                # For some reason, not providing any constraints yields the empty
                # polyhedron in Sage; it should be all of RR^whatever, IMO.
                ieqs = [ vector(ZZ, (T.ambient_dim+len(I)+1) * [0]) ]

            Q = Polyhedron(ieqs=ieqs, base_ring=QQ, ambient_dim=T.ambient_dim+len(I))

            sigma = conify_polyhedron(P.intersection(Q))
            logger.debug('Dimension of Hensel cone: %d' % sigma.dim())

            # Obtain the desired Euler characteristic via inclusion-exclusion,
            # restricted to those terms contributing to the constant term mod q-1.
            chi = sum((-1)**len(J)*alpha[I+J] for J in Subsets(M-I) if tdim[I+J] + len(I) == sigma.dim())

            if not chi:
                continue

            # NOTE: dim(P) = dim(sigma): choose any point omega in P
            # then a large point lambda in Pos^I will give (omega,lambda) in sigma.
            # Moreover, small perturbations of (omega,lambda) don't change that
            # so (omega,lambda) is an interior point of sigma inside P.

            surfs = (topologise_cone(sigma, matrix([ 
                            cat(T.integrand[0], zero_vector(ZZ,len(I))),
                            cat(T.integrand[1], vector(ZZ, len(I)*[-1]))
                            ]).transpose())
                     )

            for S in surfs:
                yield SURF(scalar=chi*S.scalar, rays=S.rays)
        
    def __repr__(self):
        return 'Subobject zeta processor\nAlgebra:\n%s\nObjects: %s\nRoot:\n%s' % (self.algebra, self.objects, self.root())


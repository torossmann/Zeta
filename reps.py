from sage.all import *

import itertools

from util import create_logger, cached_simple_method

logger = create_logger(__name__)

from convex import conify_polyhedron, is_contained_in_dual, dual_cone_as_polyhedron, RationalSet
from convex import vertex_minimiser, StrictlyPositiveOrthant, PositiveOrthant

from util import minimal_elements, principal_minors, split_off_torus

from laurent import LaurentIdeal, LaurentPolynomial

from tmplist import TemporaryList

from toric import is_nondegenerate

from torus import SubvarietyOfTorus

from abstract import ZetaDatum, ReductionError, TopologicalZetaProcessor
from surf import SURF

DEPTH_BOUND = 24

class Breakout(Exception):
    pass

class IgusaDatum(ZetaDatum):
    # General enough for representation and Igusa-type zeta functions.
    def __init__(self, ideals, depth=0):
        self.ideals = list(ideals)
        if not self.ideals:
            raise ValueError('need at least one ideal')

        self.ring = self.ideals[0].ring
        if any(J.ring != self.ring for J in self.ideals):
            raise ValueError('inconsistent base rings')
        
        self.ambient_dim = self.ring.ngens()
        self.RS = self.ideals[0].RS

        if any(I.RS != self.RS for I in self.ideals):
            raise ValueError('inconsistent rational sets')

        self.polynomials = []
        self.initials = []

        self._poly2ideal = []
        self._factors = []
        self._shifts = []
        self._ideal2poly = []

        self._depth = depth

        for i, I in enumerate(self.ideals): # I = self.ideals[i]
            self._ideal2poly.append([])
            self._factors.append([])
            self._shifts.append([])
            
            for j, f in enumerate(I.gens): # f == I.gens[j]
                k = next((k for k, g in enumerate(self.polynomials) if g.divides(f) and (f/g).is_term()), None)

                if k is None:
                    self._ideal2poly[i].append(len(self.polynomials))
                    self._factors[i].append(LaurentPolynomial(self.ring.one()))
                    self._shifts[i].append(vector(ZZ, self.ring.ngens()))

                    self.polynomials.append(f)
                    self.initials.append(I.initials[j])
                    self._poly2ideal.append([(i,j)])

                else: # f == term * self.polynomials[k]
                    self._ideal2poly[i].append(k)
                    term = f/self.polynomials[k]
                    self._factors[i].append(term)
                    self._shifts[i].append(vector(ZZ, term.exponents()[0]))

                    if I.initials[j] is None and self.initials[k] is not None:
                        I.initials[j] = term * self.initials[k]

                    if I.initials[j] is not None and self.initials[k] is None:
                        self.initials[k] = I.initials[j]/term

                        for a,b in self._poly2ideal[k]:
                            assert self.ideals[a].gens[b] == self.polynomials[k] * self._factors[a][b]
                            self.ideals[a].initials[b] = self.initials[k] * self._factors[a][b]

                    self._poly2ideal[k].append((i,j))

        # BEGIN SANITY CHECKS
        for i in xrange(len(self.ideals)):
            for j, f in enumerate(self.ideals[i].gens):
                k = self._ideal2poly[i][j]
                assert f == self.polynomials[k] * self._factors[i][j]
                if (self.ideals[i].initials[j] is not None) or (self.initials[k] is not None):
                    assert self.ideals[i].initials[j] == self.initials[k] * self._factors[i][j]

        for k, f in enumerate(self.polynomials):
            for i, j in self._poly2ideal[k]:
                assert self.ideals[i].gens[j] == f * self._factors[i][j]
                if (self.ideals[i].initials[j] is not None) or (self.initials[k] is not None):
                    assert self.ideals[i].initials[j] == self.initials[k] * self._factors[i][j]
        # END SANITY CHECKS

    def is_empty(self):
        return self.RS.is_empty()

    def weight(self):
        return sum(len(f.exponents())-1 for f in (self.initials if self.is_balanced() else self.polynomials))

    def simplify(self):
        return IgusaDatum([I.simplify() for I in self.ideals], depth=self._depth)

    def is_balanced(self):
        return not any(f is None for f in self.initials)

    def _replace_single_ideal(self, i, new, depth=None):
        # Create a new Igusa datum with RS == new.RS and i-th ideal new.
        # new.RS should better be contained in each self.ideals[j].RS;
        # otherwise initial forms should be deleted.
        return IgusaDatum([new if i == j
                           else LaurentIdeal(gens=J.gens, initials=J.initials,
                                             RS=new.RS, ring=J.ring, normalise=True)
                           for j,J in enumerate(self.ideals)],
                          depth=self._depth if depth is None else depth)

    def balance(self):
        if self.is_balanced():
            yield self
            return
        i,I = next((i,I) for i,I in enumerate(self.ideals) if not I.is_balanced())
        for J in I.balance():
            yield self._replace_single_ideal(i, J)

    @cached_simple_method
    def is_regular(self):
        if not self.is_balanced():
            return False
        return is_nondegenerate([f.num for f in self.initials],
                                all_subsets=True, all_initial_forms=False,
                                collision_handler=lambda J: setattr(self, '_coll_idx', J))

    def _low_level_reduce(self, j, a, b, ta, tb, strict):
        return self._replace_single_ideal(j, self.ideals[j].reduce(a, b, ta, tb, strict))

    def _judge_candidate(self, j, a, b, ta, tb):
        # We us the exact same approach as in subobjects.greedy_chopper.
        lt = self._low_level_reduce(j, a, b, ta, tb, strict=False).simplify()
        rt = self._low_level_reduce(j, b, a, tb, ta, strict=True).simplify()
        children = [t.simplify() for t in itertools.chain(lt.balance(), rt.balance())]
        naughty = [t for t in children if (not t.is_regular()) and t.weight() >= self.weight()]
        for t in naughty:
            t._depth += 1
            logger.info('Depth increased to %d' % t._depth)
            if t._depth > DEPTH_BOUND:
                logger.info('Exceeded the given bound for the depth of reductions.')
                return Infinity, children

        if not naughty:
            return float(0), children

        return float(sum(t.weight() for t in naughty))/ (self.weight() * len(naughty)), \
            naughty + [c for c in children if c not in naughty]

    def reduce(self, preemptive):
        if preemptive:
            raise ReductionError

        assert not self.is_regular()
        if self._depth > DEPTH_BOUND:
            raise ReductionError('Exceeded bound for reduction depth.')

        if len(self._coll_idx) == 1:
            raise ReductionError('toric singularities')

        # Find j s.t. self.ideals[j] is generated by at least two elements
        # of self.polynomials indexed by self._coll_idx.
        # 'bad' then contains at lesat 2 indices w.r.t. self.polynomials corresponding
        # to self._coll_idx

        j, bad = next(
            ( (j,list(bad)) for (j, bad) in
              ((j, Set(self._ideal2poly[j]).intersection(self._coll_idx)) for j in xrange(len(self.ideals)))
              if len(bad) >= 2),
            (None, None) )

        # Q: If the collision is spread across different ideals,
        #    should we try to find an internal simplification within
        #    one of them that gets rid of it? 
        if j is None:
            raise ReductionError('Collision involves separate ideals')

        optval, optsol = Infinity, None

        # bad from above consists of indices for self.polynomials.
        # Turn it into indices for self.ideals[j].gens
        bad = [next(b for a,b in self._poly2ideal[k] if a == j) for k in bad]

        try:
            for a,b in itertools.combinations(bad, 2):
                for ta,tb in itertools.product(self.ideals[j].initials[a].terms(),
                                               self.ideals[j].initials[b].terms()):
                    val, sol = self._judge_candidate(j, a, b, ta, tb)
                    if val < optval:
                        optval, optsol = val, sol
                    if not val:
                        raise Breakout
        except Breakout:
            pass

        if optsol is None:
            raise ReductionError('reduction failed')

        logger.info('Optimal value for reduction step: %s' % optval)
        for t in optsol:
            yield t

    def __repr__(self):
        s = 'Igusa datum of weight %d:\n' % self.weight()
        s += 'Polynomials: ' + ', '.join(str(f) for f in self.polynomials) + '\n'
        s += 'Initials: ' + ', '.join(str(f) for f in self.initials) + '\n'
        s += 'Ideals:\n'
        for i, I in enumerate(self.ideals):
            s += ('[%2d] ' % i) + str(I) + '\n'
        s += repr(self.RS)
        return s

def _sqrt(f):
    if not f:
        return f
    li = list(f.factor())
    if any(e % 2 for _, e in li):
        raise ValueError('not a square')
    return f.parent(prod(a**(e//2) for (a,e) in li))

def topologically_evaluate_monomial_integral(RS, polytopes, substitution, dims=None):
    for P in polytopes:
        if P.ambient_dim() != RS.ambient_dim:
            raise RuntimeError('dimension mismatch')

    def red(args):
        P = args[0]
        for i, Q in enumerate(args):
            if P.is_empty():
                return P
            if not i:
                continue
            P = P & Q
        return P

    for foo in itertools.product(*[vertex_minimiser(P) for P in polytopes]):
        polyhedra, alphas = zip(*foo)

        if any(P.is_empty() for P in polyhedra):
            continue

        normal_RS = RationalSet(red(polyhedra))
        if normal_RS.is_empty():
            continue

        local_RS = RS & normal_RS
        if local_RS.is_empty() or local_RS.dim() < RS.dim():
            continue

        A = matrix(ZZ, alphas)
        for surf in local_RS.topologise(
                matrix(ZZ, [ vector(ZZ, substitution[0]) * A,
                             vector(ZZ, substitution[1]) * A - vector(ZZ, A.ncols() * [1])
                             ]).transpose(), dims=dims):
            # degree < 0 check: good for reps but bad for Igusa-type zetas
            # assert any(r[0] for r in surf.rays)
            yield surf

class IgusaProcessor(TopologicalZetaProcessor):
    def __init__(self, *polynomials):
        if not polynomials:
            raise ValueError('need at least one polynomial')

        polynomials = [f if isinstance(f, LaurentPolynomial) else LaurentPolynomial(FractionField(f.parent())(f)) for f in polynomials]
        self.nvars = polynomials[0].nvars
        self.ideal = LaurentIdeal(gens=polynomials, RS=RationalSet(PositiveOrthant(self.nvars)), normalise=True)
    
    def root(self):
        return IgusaDatum([self.ideal])

    def topologically_evaluate_regular(self, datum):
        if not datum.is_regular():
            raise ValueError('need a regular datum')

        euler_cap = {}
        torus_factor_dim = {}

        N = Set(range(len(datum.polynomials)))
        _,d,_ = split_off_torus([datum.initials[i].num for i in N])
        min_dim = datum.ambient_dim - d
        
        if datum.RS.dim() < min_dim:
            logger.debug('Totally irrelevant datum')
            return
            yield

        for I in Subsets(N):
            F = [datum.initials[i].num for i in I]
            V = SubvarietyOfTorus(F, torus_dim=datum.ambient_dim)
            U,W = V.split_off_torus()
            torus_factor_dim[I] = W.torus_dim
            euler_cap[I] = U.khovanskii_characteristic() if U.is_nondegenerate() else U.euler_characteristic()
            assert torus_factor_dim[I] >= min_dim

        for I in Subsets(N):
            chi = sum((-1)**len(J) * euler_cap[I+J] for J in Subsets(N-I) if torus_factor_dim[I+J] == min_dim)
            if not chi:
                logger.debug('Vanishing Euler characteristic: I = %s' % I)
                continue
            
            I = list(I)
            polytopes = []

            id = identity_matrix(ZZ, len(I))
            def vectorise(k, vec):
                w = id[I.index(k)] if k in I else vector(ZZ,len(I))
                return vector(ZZ, list(vec) + list(w))

            assert len(datum._ideal2poly[0]) == len(datum.ideals[0].gens)
            polytopes = [Polyhedron(vertices=[ vectorise(k, datum.ideals[0].initials[m].exponents()[0]) for m,k in enumerate(datum._ideal2poly[0]) ], ambient_dim=datum.ambient_dim+len(I))]

            extended_RS = datum.RS * RationalSet(StrictlyPositiveOrthant(len(I)))

            assert all(extended_RS.ambient_dim == P.ambient_dim() for P in polytopes)
            for surf in topologically_evaluate_monomial_integral(extended_RS, polytopes, 
                                                                 [ (1,), (0,) ],
                                                                 dims=[min_dim + len(I)],
                                                                 ):
                yield SURF(scalar=chi*surf.scalar, rays=surf.rays)

    def __repr__(self):
        return 'Igusa processor. IDEAL: %s' % self.ideal

class RepresentationProcessor(TopologicalZetaProcessor):
    def __init__(self, arg):
        try:
            self.R, self.S = list(arg)
            self.algebra = None
        except TypeError:
            self.algebra = arg

    @cached_simple_method
    def root(self):
        if self.algebra is not None:
            self.R, self.S = self.algebra._commutator_matrices()
        self.ring = self.R.base_ring()

        d = self.ring.ngens()
        self.d = d

        polyhedra = []
        for i in xrange(d):
            eqns = [
                (i+1) * [0] + [1] + (d-i-1) * [0]
            ]
            ieqs = [
                [-1] + j * [0] + [1] + (d-j-1) * [0]
                for j in xrange(i)
            ]
            ieqs += [
                (j+1) * [0] + [1] + (d-j-1) * [0]
                for j in xrange(i+1,d)
            ]
            polyhedra.append(Polyhedron(eqns=eqns, ieqs=ieqs))
        self.RS = RationalSet(polyhedra, ambient_dim=d)

        F = FractionField(self.ring)
        two_u = matrix(F, self.R).rank() # self.R.rank()
        if two_u % 2:
            raise RuntimeError('this is odd')
        self.u = two_u // 2
        self.v = matrix(F, self.S).rank() # self.S.rank()

        if not d:
            return

        F = [
            LaurentIdeal(
                gens = [LaurentPolynomial(_sqrt(f)) for f in principal_minors(self.R, 2*j)],
                RS = self.RS,
                normalise = True)
            for j in range(0, self.u+1)
        ]

        G = [
            LaurentIdeal(
                gens = [LaurentPolynomial(g) for g in self.S.minors(j)],
                RS = self.RS,
                normalise = True)
            for j in range(0, self.v+1)
            ]

        oo = self.u + self.v + 2

        # On pairs:
        # The first component is used as is, the second is multiplied by the extra
        # variable. Note that index 0 corresponds to {1} and index oo to {0}.
        # We skip the |F_1|/|F_0 cap xF_1| factor which is generically trivial.
        self.pairs = (
            [(oo,0)] +
            [(i,oo) for i in xrange(2,self.u)] + [(i+1,i) for i in xrange(1,self.u)] +
            [(i,oo) for i in xrange(self.u+2,self.u+self.v+1)] +
            [(i+1,i) for i in xrange(self.u+1,self.u+self.v+1)]
            )
        # Note: q^b t^a really corresponds to a*s - b, in contrast to subobjects, where
        # the (-1)-shift coming from Jacobians is included.
        # This also means we don't have to manually add (-1)s for extra variables.
        self.integrand = (
            (self.u,) + (self.u-2)*(1,) + (self.u-1)*(-1,) + (2*self.v-1)*(0,),
            (self.d+1-self.v,) + (2*self.u-3)*(0,) + (self.v-1)*(-1,) + self.v*(1,)
            )

        self.datum = IgusaDatum(F + G + [LaurentIdeal(gens=[], RS=self.RS, ring=FractionField(self.ring))])
        self.datum = self.datum.simplify()

        return self.datum

    def topologically_evaluate(self, shuffle=False):
        return (SR(1) + TopologicalZetaProcessor.topologically_evaluate(self, shuffle=shuffle)).factor()

    def topologically_evaluate_regular(self, datum):
        if not datum.is_regular():
            raise ValueError('need a regular datum')

        euler_cap = {}
        torus_factor_dim = {}

        N = Set(range(len(datum.polynomials)))
        
        _,d,_ = split_off_torus([datum.initials[i].num for i in N])
        min_dim = datum.ambient_dim - d

        # NOTE: triangulation/"topologisation" of RationalSet instances only
        # considers cones of maximal dimension.
        if datum.RS.dim() <= min_dim - 2:
            return
            yield

        if datum.RS.dim() >= min_dim:
            raise RuntimeError('this should be impossible')

        for I in Subsets(N):
            F = [datum.initials[i].num for i in I]
            V = SubvarietyOfTorus(F, torus_dim=datum.ambient_dim)
            U,W = V.split_off_torus()
            torus_factor_dim[I] = W.torus_dim

            assert torus_factor_dim[I] >= min_dim

            if W.torus_dim > min_dim:
                continue
            euler_cap[I] = U.khovanskii_characteristic() if U.is_nondegenerate() else U.euler_characteristic()

        for I in Subsets(N):
            chi = sum((-1)**len(J) * euler_cap[I+J] for J in Subsets(N-I) if torus_factor_dim[I+J] == min_dim)
            if not chi:
                continue
            
            I = list(I)
            id = identity_matrix(ZZ, len(I))
            def vectorise(first, k, vec):
                w = id[I.index(k)] if k in I else vector(ZZ,len(I))
                return vector(ZZ, [first] + list(vec) + list(w))
            
            polytopes = []
            for (i,j) in self.pairs:
                vertices = [vectorise(0, k, datum.ideals[i].initials[m].exponents()[0]) for m,k in enumerate(datum._ideal2poly[i])] +\
                           [vectorise(1, k, datum.ideals[j].initials[m].exponents()[0]) for m,k in enumerate(datum._ideal2poly[j])]
                polytopes.append(Polyhedron(vertices=vertices, ambient_dim=1+datum.ambient_dim+len(I)))
            extended_RS = (RationalSet(StrictlyPositiveOrthant(1)) * datum.RS *
                           RationalSet(StrictlyPositiveOrthant(len(I))))

            for surf in topologically_evaluate_monomial_integral(extended_RS, polytopes,
                                                                 self.integrand, dims=[min_dim+len(I)]):
                yield SURF(scalar=chi*surf.scalar, rays=surf.rays)

    def __repr__(self):
        if self.root() is not None:
            s = 'Representation processor:\n'
            s += 'Base ring: %s\n' % self.datum.ring
            s += 'R =\n' + str(self.R) + '\n'
            s += 'u = %d\n' % self.u
            s += 'S =\n' + str(self.S) + '\n'
            s += 'v = %d\n' % self.v
            s += 'Root:\n%s' % self.datum
            return s
        else:
            return 'Trivial representation processor'
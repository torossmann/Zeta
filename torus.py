"""
Closed subvarieties of algebraic tori.
"""

from sage.all import *

from itertools import chain
from convex import mixed_volume
from util import normalise_laurent_polynomial, squarefree_part, monomial_exp, \
    terms_of_polynomial, cached_simple_method, split_off_torus

from common import symbolic_count_varieties

import common

from util import create_logger, MyCompositions

logger = create_logger(__name__)

def symbolic_variable(V):
    try:
        idx = symbolic_count_varieties.index(V)
    except ValueError:
        idx = len(symbolic_count_varieties)
        symbolic_count_varieties.append(V)
    return var('sc_%d' % idx)

# def monomial_sat(I):
#     R = I.ring()
#     J = R.ideal(prod(R.gens()))
#     sat, _ = singular.sat(I._singular_(), J._singular_())
#     _, sat = singular.mstd(sat)
#     return R.ideal(sat)

class CountException(Exception):
    pass

class SubvarietyOfTorus:
    def __init__(self, polynomials=None, torus_dim=None):
        if not polynomials:
            if torus_dim is None:
                raise ValueError('Need to specify the dimension')
            self.torus_dim = torus_dim
            self.ring = PolynomialRing(QQ, self.torus_dim, 'x')
            self.polynomials = []
            return

        R = polynomials[0].parent()
        if (torus_dim is not None) and (torus_dim != R.ngens()):
            raise ValueError('Supplied dimension does not match the given polynomials')
        self.torus_dim = R.ngens()
        self.ring = PolynomialRing(QQ, self.torus_dim, 'x')

        if self.torus_dim == 0:
            # Some things like GCDs fail for polynomial rings in 0 variables. *sigh*
            self.polynomials = [self.ring.one()] if any(f for f in polynomials) else []
            return

        # Map everything into our 'reference polynomial ring' and normalise.
        theta = R.hom(self.ring.gens())
        nm = lambda f: normalise_laurent_polynomial(f/f.lc())
        polynomials = list(set([nm(theta(f)) for f in polynomials if f != 0]))
        self.polynomials = [self.ring.one()] if (1 in polynomials) else polynomials
        return

    def __eq__(self, other):
        if not self.torus_dim == other.torus_dim:
            return False
        return sorted(self.polynomials) == sorted(other.polynomials)

    def _solvable_conditions(self):
        """
        Produce all (i,x,g) such that F[i] == 0 is equivalent to x == g;
        here x is one of the defining variables and g is a Laurent polynomial
        which only involves variables != x.
        """

        vars = self.ring.gens()
        F = self.polynomials

        for i in xrange(len(F)):
            for x in vars:
                terms = terms_of_polynomial(F[i])
                cand = [t for t in terms if x.divides(t)]
                if len(cand) != 1:
                    continue

                t0 = cand[0]
                if (x**2).divides(t0):
                    continue

                g = -sum(t for t in terms if t != t0)/(t0//x)
                logger.debug('[%d] %s == 0 is equivalent to %s == %s' % (i, F[i], x, g))
                yield (i, x, g)

    def _isolated_variables(self):
        """
        Produce all (i,x,u,v) such that
            (1) F[i] == 0 is equivalent to u == v * x,
            (2) x does not occur in u, v, nor in F[j] for i != j.
        """
        
        F = self.polynomials
        for x in self.ring.gens():
            seen = False
            cand = None

            for i,f in enumerate(F):
                vterms = [t//x for t in terms_of_polynomial(f) if x.divides(t)]
                if not vterms:
                    continue

                if seen or any(x.divides(t) for t in vterms):
                    cand = None
                    break

                seen = True
                v = sum(vterms)
                cand = (i,x,v*x-f,v)
            if not cand is None:
                yield cand

    @cached_simple_method
    def split_off_torus(self):
        """
        Given non-zero polynomials F defining a a subvariety V of T^n,
        we seek to find polynomials G in d variables such that
        V ~ W * T^(n-d), where W is defined by G. Returns W and T^(n-d).
        The number d is the dimension of the Minkowski sum of the Newton
        polytopes of the polynomials in F.
        """
        G,d, _ = split_off_torus(self.polynomials)
        return SubvarietyOfTorus(G, torus_dim=d), SubvarietyOfTorus(torus_dim=self.torus_dim-d)

    def simplify_defining_equations(self):
        F = self.polynomials[:]

        if self.torus_dim == 1:
            F = [gcd(F)]
        F = [squarefree_part(f) for f in F]

        # # If the saturated generating set is 'smaller', use that.
        # G = monomial_sat(self.ring.ideal(F)).gens()
        # if sum(len(f.coefficients()) for f in G) < sum(len(f.coefficients()) for f in F):
        #   logger.debug('Using saturated generators.')
        #    F = G

        # 'mu' measures the 'size' of a polynomial for our greedy algorithm.
        mu = lambda f: len(f.coefficients()) 
        changed = True
        while changed:
            changed = False

            for i in xrange(len(F)):
                if F[i] == 0:
                    continue
                if F[i] == 1 or F[i].is_monomial():
                    logger.debug('Variety is empty.')
                    return SubvarietyOfTorus(polynomials=[self.ring.one()],
                                             torus_dim=self.torus_dim)

                # Discard multiplicities and monomial factors.
                F[i] = self.ring.prod(f for f,_ in F[i].factor() if not f.is_monomial())
                
                for j in xrange(len(F)):
                    if i == j:
                        continue

                    if F[j] == 0:
                        continue

                    # Important invariant: non-zero polynomials in F are monic.

                    # First attempt: Polynomial division.
                    _, r = F[i].quo_rem(F[j])
                    r = squarefree_part(r)

                    if mu(r) < mu(F[i]):
                        logger.debug('(quo/rem) Replacing F[%d]=%s by %s' % (i,F[i],r))
                        F[i] = r if not r else normalise_laurent_polynomial(r/r.lc())
                        changed = True
                        continue

                    # Second attempt: reduction.
                    # We try ALL conceivable pairs.
                    reduction_performed = True
                    while reduction_performed:
                        reduction_performed = False
                        for ti in terms_of_polynomial(F[i]):
                            for tj in terms_of_polynomial(F[j]):
                                g = gcd(ti,tj)

                                r = (tj//g) * F[i] - (ti//g) * F[j]
                                r = squarefree_part(r)

                                if mu(r) < mu(F[i]):
                                    logger.debug('(reduce) Replacing F[%d]=%s by %s' % (i,F[i],r))
                                    logger.debug('(reduce) Using term %s of F[%d] and term %s of F[%d]'
                                         % (ti,i,tj,j))
                                    F[i] = r if not r else normalise_laurent_polynomial(r/r.lc())
                                    changed = True
                                    reduction_performed = True
                                    break
                            else:
                                continue
                            break

        F = [f for f in F if f != 0]
        return SubvarietyOfTorus(polynomials=F, torus_dim=self.torus_dim)

    @cached_simple_method
    def khovanskii_characteristic(self):
        """
        Given k polytopes P[0], ..., P[k-1] in n-space, compute the sum 
        (-1)^(n+k) * n! * MV(P[0], ..., P[0], P[1], ..., P[1], ...)
        over all compositions of n.
        This number is an integer which is equal to the Euler characteristic
        of the subvariety of TT^n defined by sufficiently non-degenerate
        (Laurent) polynomials with Newton polytopes P[0], ..., P[k-1].
        """

        if not self.polynomials:
            return 1 if self.torus_dim == 0 else 0
        elif any(f.is_constant() and f != 0 for f in self.polynomials):
            return 0

        P = [f.newton_polytope() for f in self.polynomials]
        k = len(P)

        n = P[0].ambient_dim()
        if any(q.ambient_dim() != n for q in P):
            raise TypeError('All polytopes must have the same ambient dimension')

        if k > n:
            return 0
        
        return (
            (-1)**(n+k) * factorial(n) *
            sum(mixed_volume(chain.from_iterable([q] * a for (q, a) in zip(P, c)))
                for c in MyCompositions(n, length=k)
                )
            )

    @cached_simple_method
    def is_nondegenerate(self):
        if not self.polynomials:
            return True
        from toric import is_nondegenerate
        return is_nondegenerate(self.polynomials, all_subsets=False, all_initial_forms=True)

    def _count_general(self, level):
        # Levels:
        # -1 - Euler characteristic
        #  0 - polynomial in q
        #  1 - polynomial in q or roots of univariate polynomials
        #  2 - general closed subvarieties of tori

        euler = level < 0 # == only compute euler characteristic 
        q = int(1) if euler else var('q')

        logger.debug('Initial polynomials: %s' % self.polynomials)
        
        V,W = self.simplify_defining_equations().split_off_torus()
       
        if W.torus_dim > 0:
            logger.debug('Split off torus factor of dimension %d' % W.torus_dim)

        logger.debug('Simplified polynomials: %s' % self.polynomials)

        if W.torus_dim > 0:
            return 0 if euler else V._count_general(level) * (q-1)**W.torus_dim

        V = V.simplify_defining_equations()
        if not V.polynomials:
            return (q-1)**V.torus_dim # note: 0**0 == 1
        elif any(f.is_constant() and f != 0 for f in V.polynomials):
            return 0 if euler else SR(0) # empty set
        elif euler and V.is_nondegenerate():
            logger.debug('The variety is Khovanskii-non-degenerate')
            return V.khovanskii_characteristic()

        if not euler and V.torus_dim == 1:
            assert len(V.polynomials) == 1
            f = V.polynomials[0]
            if len(f.factor()) == f.degree(): # check if f splits completely over QQ
                return SR(f.degree())
            if level == 0:
                raise CountException('cannot handle number fields when level == 0')
            else:
                return symbolic_variable(V)

        F = V.polynomials
        I = range(len(F))
            
        logger.debug('Factoring polynomials')
        
        # Try to use inclusion-exclusion and a factorisation to count points.
        for i,f in enumerate(F):
            fac = [g for g,_ in f.factor()] # drop multiplicities
            if len(fac) == 1:
                continue

            g = fac[0]
            h = V.ring.prod(fac[1:])

            li = [g if j == i else F[j] for j in range(len(F))]
            xi = [h if j == i else F[j] for j in range(len(F))]
            zi = li + [h]
            
            U = SubvarietyOfTorus(li, V.torus_dim)
            W = SubvarietyOfTorus(xi, V.torus_dim)
            Z = SubvarietyOfTorus(zi, V.torus_dim)

            try:
                res = U._count_general(level) + W._count_general(level) - Z._count_general(level)
            except CountException:
                pass
            else:
                logger.debug('Successfully used a factorisation.')
                logger.debug('U = %s' % U.polynomials)
                logger.debug('W = %s' % W.polynomials)
                logger.debug('Z = %s' % Z.polynomials)
                return res
            
        logger.debug('Trying to decompose the variety...')
        for (i,x,g) in V._solvable_conditions():
            # NOTE: We need to specify the number of variables in the following
            # line for otherwise Sage might use a UNIVARIATE polynomial ring;
            # these behave differently.
            S = PolynomialRing(QQ, V.torus_dim-1, [y for y in V.ring.gens() if y != x])
            li = [S(normalise_laurent_polynomial(F[j].subs({x: g})))
                  for j in I if j != i]
            U = SubvarietyOfTorus(li, V.torus_dim-1)
            W = SubvarietyOfTorus([S(normalise_laurent_polynomial(g))] + li)
            try:
                res = U._count_general(level) - W._count_general(level)
            except CountException:
                pass
            else:
                logger.debug('Successfully decomposed variety.')
                logger.debug('Solvable condition: (%d, %s, %s)' % (i,x,g))
                logger.debug('U = %s' % U.polynomials)
                logger.debug('W = %s' % W.polynomials)
                return res

        logger.debug('Trying to isolate a variable...')
        for (i,x,u,v) in V._isolated_variables():
            # When F[i] == 0 is equivalent to x*v==u and x doesn't occur in
            # any other F[j], there are two cases:
            # (1) On the subvariety v==0, x is arbitrary so this part has Euler
            # characteristic zero.
            # (2) On v != 0, x == u/v is completely determined by the
            # remaining variables and the implicit condition u != 0.

            S = PolynomialRing(QQ, V.torus_dim-1, [y for y in V.ring.gens() if y != x])
            li = [S(F[j]) for j in I if j != i]

            U = SubvarietyOfTorus(li, V.torus_dim-1)
            Wu = SubvarietyOfTorus([S(u)]+li, V.torus_dim-1)
            Wv = SubvarietyOfTorus([S(v)]+li, V.torus_dim-1)
            Z = SubvarietyOfTorus([S(u), S(v)] + li, V.torus_dim-1)

            try:
                res = U._count_general(level) - Wu._count_general(level) - Wv._count_general(level) + q * Z._count_general(level)
            except CountException:
                pass
            else:
                logger.debug('Succesfully isolated a variable.')
                logger.debug('Isolated variable data: (%d, %s, %s, %s)' % (i,x,u,v))
                logger.debug('U = %s' % U.polynomials)
                logger.debug('Wu = %s' % Wu.polynomials)
                logger.debug('Wv = %s' % Wv.polynomials)
                logger.debug('Z = %s' % Z.polynomials)
                return res
       
        logger.debug('SubvarietyOfTorus._count_general failed. Defining polynomials: %s' % self.polynomials)

        if level < 2:
            raise CountException('failed to %s' % ('compute Euler characteristic' if euler else 'count points'))
        else:
            return symbolic_variable(self)

    @cached_simple_method
    def euler_characteristic(self):
        return self._count_general(level=-1)
            
    @cached_simple_method
    def count(self):
        for i in ([0,1,2] if common.symbolic else [0]):
            try:
                return SR(self._count_general(level=i)).expand()
            except CountException:
                logger.debug('count (level=%d) failed: %s' % (i, self))
        raise CountException('Failed to count number of rational points. Try switching to symbolic mode.')
        
    def __str__(self):
        if self.polynomials:
            return 'Subvariety of %d-dimensional torus defined by %s' % (self.torus_dim, self.polynomials)
        else:
            return 'Torus of dimension %d' % self.torus_dim

    __repr__ = __str__
 
def Torus(n):
    return SubvarietyOfTorus(torus_dim=n)

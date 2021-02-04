"""
Closed subvarieties of algebraic tori.
"""

from sage.all import *

from itertools import chain
from convex import mixed_volume
from util import normalise_laurent_polynomial, squarefree_part, monomial_exp, \
    terms_of_polynomial, cached_simple_method
import toric

from util import create_logger
logger = create_logger(__name__)

# def monomial_sat(I):
#     R = I.ring()
#     J = R.ideal(prod(R.gens()))
#     sat, _ = singular.sat(I._singular_(), J._singular_())
#     _, sat = singular.mstd(sat)
#     return R.ideal(sat)

class EulerException(Exception):
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
            self.polynomials = [one(self.ring)] if any(f for f in polynomials) else []
            return

        # Map everything into our 'reference polynomial ring' and normalise.
        theta = R.hom(self.ring.gens())
        nm = lambda f: normalise_laurent_polynomial(f/f.lc())
        polynomials = [nm(theta(f)) for f in polynomials if f != 0]
        self.polynomials = [one(self.ring)] if (1 in polynomials) else polynomials
        return

    def _solvable_conditions(self):
        """
        Produce all (i,x,g) such that F[i] == 0 is equivalent to x == g;
        here x is one of the defining variables and g is a Laurent polynomial
        involving involving only variables != x.
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

        if not self.polynomials:
            return (
                SubvarietyOfTorus(torus_dim=0),
                SubvarietyOfTorus(torus_dim=self.torus_dim)
                )

        F = self.polynomials
        R = self.ring
        n = R.ngens()

        v = {f:vector(ZZ,f.exponents()[0]) for f in F}
        logger.debug('Shifts: %s' % v)

        submodule = (ZZ**n).submodule(
            chain.from_iterable((vector(ZZ,e)-v[f] for e in f.exponents())
                                for f in F)
            )

        # Q: Why does 'basis_matrix' produce a matrix over QQ? Makes no sense!
        D,S,T = matrix(ZZ, submodule.basis_matrix()).smith_form()

        d = submodule.rank()
        logger.debug('Active submodule has rank %d' % d)

        K = FractionField(R)
        Rd = PolynomialRing(QQ, d, R.gens()[:d])
        G = []
        for f in F:
            # WARNING: T can have large entries, overflowing Singular's exponents
            G.append(Rd(
                    normalise_laurent_polynomial(
                        K(f([monomial_exp(K,e) for e in T.rows()]))
                        )
                    ))

        return (
            SubvarietyOfTorus(G, torus_dim=d),
            SubvarietyOfTorus(torus_dim=n-d)
            )

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
                    return SubvarietyOfTorus(polynomials=[one(self.ring)],
                                             torus_dim=self.torus_dim)
                for j in xrange(len(F)):
                    if i == j:
                        continue

                    if F[j] == 0:
                        continue

                    # Important invariant: non-zero polynomials in F are monic.

                    # First attempt: Polynomial division.
                    _, r = F[i].quo_rem(F[j])
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
                                if g == 1:
                                    continue
                                r = (tj//g) * F[i] - (ti//g) * F[j]
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
                for c in Compositions(n, length=k)
                )
            )

    @cached_simple_method
    def is_nondegenerate(self):
        if not self.polynomials:
            return True
        return toric.is_nondegenerate(self.polynomials, all_subsets=False)


    @cached_simple_method
    def euler_characteristic(self):
        V,W = self.simplify_defining_equations().split_off_torus()

        if W.torus_dim > 0:
            return 0

        V = V.simplify_defining_equations()
        if not V.polynomials:
            return 1 if V.torus_dim == 0 else 0
        elif any(f.is_constant() and f != 0 for f in V.polynomials):
            return 0
        elif V.is_nondegenerate():
            logger.debug('The variety is Khovanskii-non-degenerate')
            return V.khovanskii_characteristic()

        logger.debug('Trying to decompose the variety...')
        F = V.polynomials
        I = range(len(F))

        # TODO: use torus automorphisms, e.g. invert some variables

        for (i,x,g) in V._solvable_conditions():

            # Suppose F[i] == 0 is equivalent to x == g(other vars), where g
            # is a Laurent polynomial.
            # Then the subvariety of Torus(n) defined by F is isomorphic to
            # the complement of g == 0 in the subvariety of Torus(n-)1 defined
            # by all F[j](x = g) for j != i.

            # NOTE: We need to specify the number of variables in the following
            # line for otherwise Sage might use a UNIVARIATE polynomial ring;
            # these behave differently.

            S = PolynomialRing(QQ, V.torus_dim-1, [y for y in V.ring.gens() if y != x])

            # Rewrite remaining polynomials in the remaining variables.
            li = [S(normalise_laurent_polynomial(F[j].subs({x: g})))
                  for j in I if j != i]

            # NOTE: We specify torus_dim in the following in case li == [].
            U = SubvarietyOfTorus(li, V.torus_dim-1)
            W = SubvarietyOfTorus([S(normalise_laurent_polynomial(g))] + li)

            try:
                return U.euler_characteristic() - W.euler_characteristic()
            except EulerException:
                pass
            else:
                logger.debug('Successfully decomposed variety.')

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
                return (U.euler_characteristic()
                        - Wu.euler_characteristic()
                        - Wv.euler_characteristic()
                        + Z.euler_characteristic())
                        
            except EulerException:
                pass
            else:
                logger.debug('Succesfully isolated a variable.')


        # Now would be a good time to use a general-purpose method
        # for computing Euler characteristics...

        logger.info('Failed to compute Euler characteristic')
        logger.info('Defining polynomials: %s' % self.polynomials)

        raise EulerException('Cannot compute Euler characteristic')
        
    def __str__(self):
        if self.polynomials:
            return 'Subvariety of %d-dimensional torus defined by %s' % (self.torus_dim, self.polynomials)
        else:
            return 'Torus of dimension %d' % self.torus_dim
 
def Torus(n):
    return SubvarietyOfTorus(torus_dim=n)

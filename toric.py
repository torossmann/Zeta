"""This module provides basic functionality for toric data.
"""

from sage.all import *

from convex import conify_polyhedron, \
    is_contained_in_dual, dual_cone_as_polyhedron, \
    inner_open_normal_fan, get_point_in_polyhedron, \
    DirectProductOfPolyhedra, linear_image_of_polyhedron

from util import normalise_poly, monomial_log, \
    subpolynomial_meet, is_subpolynomial, initial_form_by_direction, \
    unzip, cached_simple_method, minimal_elements, split_off_torus

import common
import itertools

from util import create_logger
logger = create_logger(__name__)

def relative_initial_forms(F, polyhedron=None, split=True):
    if not F:
        raise ValueError('need non-empty collection of polynomials')

    if split:
        G, d, A = split_off_torus(F)
        N = sum(g.newton_polytope() for g in G)
        n = A.nrows()
    else:
        N = sum(f.newton_polytope() for f in F)
        n = N.ambient_dim()

    if polyhedron is None:
        polyhedron = Polyhedron(ieqs=[(n+1)*(0,)])

    for Q in inner_open_normal_fan(N):
        if split:
            Q = linear_image_of_polyhedron(DirectProductOfPolyhedra(Q, Polyhedron(ieqs=[(n-d+1)*(0,)])),
                                           A.transpose())
        Q &= polyhedron
        if Q.dim() == -1:
            continue
        y = get_point_in_polyhedron(Q)
        yield [initial_form_by_direction(f, y) for f in F], Q

    
def belongs_to_radical(f, I):
    """Test if f in I.radical().
    """

    R = PolynomialRing(QQ, I.ring().ngens()+1, I.ring().variable_names() + ('Zoo',))
    Zoo = R.gens()[-1]
    J = R.ideal([R(g) for g in I.gens()] + [R(1) - Zoo*R(f)])
    return [R(1)] == J.groebner_basis(algorithm='singular' if common.plumber else '')

def is_nondegenerate(F, all_subsets=True, all_initial_forms=True, collision_handler=None):
    # NOTE: Setting all_subsets=False gives exactly Khovanskii's original
    # non-degeneracy condition.

    logger.debug('Original polynomials: %s' % F)
    if not F:
        return True

    if 0 in F:
        raise NotImplementedError()

    for G, _ in relative_initial_forms(F) if all_initial_forms else [(F,None)]:
        # NOTE: we could do the torus factor splitting for each subset separately.
        G, _, _ = split_off_torus(G)
        logger.debug('Restricted polynomials: %s' % G)

        R = G[0].parent()
        jac = jacobian(G, R.gens())

        idx = [i for i in xrange(len(G)) if not G[i].is_monomial()]
        if not all_subsets and len(idx) < len(G):
            continue # empty variety!

        logger.debug('Active indices: %s' % idx)
        S = Subsets(idx) if all_subsets else [idx]

        for J in S:
            if not J:
                continue
            I = R.ideal([G[j] for j in J] + matrix(R,[jac[j] for j in J]).minors(len(J)))
            if not belongs_to_radical(prod(R.gens()), I):
                logger.debug('Collision: %s' % J)
                if collision_handler is not None:
                    collision_handler(J)
                return False
    return True

class ToricDatum:
    """A toric datum consists of
    (1) a rational polyhedron in some valuation space,
    (2) an integrand given by two Laurent vectors encoding Laurent monomials,
    (3) polynomial divisibility conditions with monomial left-hand sides
        Laurent polynomials representing, and
    (4) partial markings of initial forms among the right-hand sides.
    """
    def __init__(self, ring, integrand, cc, initials, polyhedron, depth=0):
        """Initialise a toric datum.

        'ring' should be a polynomial ring over QQ, the number of variables of which
        is taken to be the ambient dimension.

        When evaluating associated integrals, we will sum over
        t^(integrand[0] * y) * p^(integrand[1] * y) with y in polyhedron.

        'cc' should be a list-like object consisting of pairs (m,f) with 'm'
        monomial and 'f' in 'ring'.

        Everything is copied and normalised. We may further replace the given
        toric datum by an equivalent one.
        
        If it is set, 'initials' should be a list-like object s.t. initials[i]
        is either 'None' or a sub-polynomial of cc[i][1]. It is then assumed
        but not checked that initials[i] is the initial form of cc[i][1]
        throughout 'polyhedron'.
        """

        # Bookkeeping

        self.ring = ring
        self.ambient_dim = ring.ngens()
        self.integrand = tuple(integrand)
        self.polyhedron = polyhedron
        self._coll_idx = None
        self._ordered = False
        self._depth = depth

        # Empty polyhedra can easily arise as part of reduction
        if self.polyhedron.dim() == -1:
            self.cc, self.lhs, self.rhs, self.initials = [], [], [], []
            return

        if cc is None:
            cc = []
        initials = len(cc)*[None] if initials is None else initials[:]

        if len(cc) != len(initials):
            raise TypeError('The number of initials has to be the same as the number of conditions')

        # Discard conditions 'm || 0'.
        # We shouldn't remove 'constant || f' unless we know that everything
        # is integral.
        # This code fails if '0' is a LHS which should not be allowed anyway.
        idx = [i for i in xrange(len(cc)) if (cc[i][1] != Integer(0))] # and (not cc[i][0].is_constant())]
        cc, initials = [cc[i] for i in idx], [initials[i] for i in idx]

        # Normalise everything. If initials are given, we use their leading terms
        # instead of those of the full RHS.
        # We also set the initials of monomials.
        self.lhs, self.rhs, self.initials = [], [], []
        for i in xrange(len(cc)):
            self.lhs.append(normalise_poly( cc[i][0]) )
            if initials[i] is None:
                f = normalise_poly( cc[i][1] )
                self.rhs.append(f)
                self.initials.append( f if f.is_monomial() else None )
            else:
                self.initials.append( initials[i]/initials[i].lc() )
                self.rhs.append( cc[i][1]/initials[i].lc() )
            
        self.cc = zip(self.lhs, self.rhs)
        
        # Some sanity checks.
        for i in xrange(len(self.cc)):
            if not self.lhs[i].is_monomial():
                raise TypeError('LHS has to consist of monomials')
            if not(self.initials[i] is None) and not(is_subpolynomial(self.rhs[i], self.initials[i])):
                raise TypeError('initial forms need to be sub-polynomials')
            
    def length(self):
        """Return the number of divisibility conditions.
        """
        return len(self.cc)

    def weight(self):
        return sum(len(r.monomials())-1 for r in self.rhs)

    def _purge_multiples(self):
        if self.is_empty():
            return self

        D = conify_polyhedron(self.polyhedron)
        F = FractionField(self.ring)
        def lte(i,j):
            if i == j:
                return True
            rat = F(self.rhs[j]*self.lhs[i]/self.rhs[i]/self.lhs[j])
            try:
                alpha = monomial_log(rat.numerator()) - monomial_log(rat.denominator())
            except ValueError:
                return False
            return is_contained_in_dual(Cone([alpha]), D)

        mins = minimal_elements(range(len(self.rhs)), lte)
        if len(mins) == len(self.rhs):
            return self
        return ToricDatum(self.ring, self.integrand,
                                  [(self.lhs[i],self.rhs[i]) for i in mins],
                                  [self.initials[i] for i in mins],
                                  self.polyhedron, depth=self._depth)


    def simplify(self):
        """Simplify a toric datum.
        
        We do the following:
        (1) Move pseudo-monomial divisibility conditions into the polyhedron.
        (2) Perform support reduction using the polyhedron.
        (3) Scan for divisibility relations.
        """

        try:
            if self._is_simple:
                return self
        except AttributeError:
            pass

        # T is the current toric datum
        T = self

        cnt = 0
        while true:
            cnt += 1
            if cnt > 2:
                logger.info('Simplification entered round %d' % cnt) # e.g. triggered for Perm(123)

            logger.debug('Looping. Current datum:\n%s' % T)

            # T = T.divide_out_variables()

            changed = false
            polyhedron = T.polyhedron
            new_cc, new_initials = [], []

            # Step 1: Move pseudo-monomial conditions into the polyhedron.
            # We say that a condition is pseudo-monomial if it's initial form is monomial.

            idx_mon = [i for i in xrange(len(T.cc)) if (T.initials[i] is not None) and T.initials[i].is_monomial()]
            idx_nonmon = [i for i in xrange(len(T.cc)) if not i in idx_mon]
            logger.debug('Number of conditions: %d (pseudo-monomials: %d)' % (len(T.cc),len(idx_mon)))

            if len(idx_mon) > 0:
                logger.debug('Shrinking polyhedron.')

                polyhedron &= dual_cone_as_polyhedron([monomial_log(T.initials[i]) - monomial_log(T.lhs[i]) for i in idx_mon])

                # NOTE: we don't set 'changed = True' at this point. No need.

            # Step 2: 
            # For each non-monomial condition, remove terms divisible by the
            # LHS within the polyhedron
            cone = conify_polyhedron(polyhedron)
            for i in idx_nonmon:  # or 'xrange(len(T.cc))', to be safe
                lhs, rhs = T.cc[i] ; init = T.initials[i]

                g = gcd(lhs,rhs)
                lhs, rhs = lhs//g, rhs//g
                if not(init is None):
                    init //= g

                # Find redundant terms of 'rhs'.
                mon, coeff = rhs.monomials(), rhs.coefficients()
                idx_red = [ j for j in xrange(len(mon))
                            if is_contained_in_dual(Cone([monomial_log(mon[j]) - monomial_log(lhs)], lattice=ZZ**T.ambient_dim), cone) ]

                # Case a: No term of 'rhs' is redundant
                if len(idx_red) == 0:
                    new_cc.append((lhs, rhs)) ; new_initials.append(init)
                    continue

                changed = true

                # Case b: (lhs || rhs) follows from the monomial conditions.
                if len(idx_red) == len(mon):
                    logger.debug('Redundant condition: %s || %s' % (lhs,rhs))
                    continue
                
                # Case c: lhs || rhs can be simplified but not removed.
                logger.debug('Condition %s || %s becomes...')

                red = sum(coeff[k]*mon[k] for k in idx_red) # = redundant form of 'rhs'
                rhs -= red

                g = gcd(lhs,rhs)
                lhs, rhs = lhs//g, rhs//g

                if not(init is None):
                    # NOTE:
                    # If init != None and some term of init is redundant, then the
                    # entire condition 'lhs || rhs' has to be redundant.
                    if subpolynomial_meet(init, red) != Integer(0):
                        raise RuntimeError('Impossible redundancy. This should never happen.')

                    init = (init - subpolynomial_meet(init, red))//g
                    init = None if init==Integer(0) else init

                    # Sanity check.
                    if not(is_subpolynomial(rhs, init)):
                        raise RuntimeError('I messed up an initial form')
                    
                logger.debug('... %s || %s' % (lhs,rhs))
                new_cc.append((lhs,rhs)) ; new_initials.append(init)

            T = ToricDatum(ring=T.ring, integrand=T.integrand,
                                    cc=new_cc, initials=new_initials,
                                    polyhedron=polyhedron, depth=self._depth)

            if not changed:
                break

        T = T._purge_multiples()
        T._is_simple = True
        return T

    def is_empty(self):
        return self.polyhedron.dim() == -1

    @cached_simple_method
    def is_balanced(self):
        """Check if the toric datum is known to be balanced.
        """
        return None not in self.initials

    def is_ordered(self):
        return self._ordered

    def balance(self, strategy='min'):
        if self.is_balanced():
            yield self
            return

        idx, weights = unzip((i,len(f.monomials())) for i,f in enumerate(self.rhs) if self.initials[i] is None)

        if strategy == 'full':
            J = idx
        elif strategy == 'min':
            J = [ idx[weights.index(min(weights))] ]
        elif strategy == 'max':
            J = [ idx[weights.index(max(weights))] ]
        else:
            raise TypeError('unknown balancing strategy')

        for F, Q in relative_initial_forms([self.rhs[j] for j in J], self.polyhedron):
            new_initials = self.initials[:]
            for (j,f) in itertools.izip(J, F):
                new_initials[j] = f
            yield ToricDatum( ring=self.ring, integrand=self.integrand,
                              cc=self.cc, initials=new_initials,
                              polyhedron=Q, depth=self._depth )

    def order(self):
        if self._ordered:
            yield T
            return

        if not self.is_balanced():
            raise ValueError('Cannot order unbalanced conditions')

        alpha = [ monomial_log(self.initials[i].monomials()[0])-monomial_log(self.lhs[i])
                  for i in range(len(self.rhs)) ]

        I = range(len(self.rhs)) if not self._coll_idx else self._coll_idx
        for pi in itertools.permutations(I, len(I)):
            polyhedron = self.polyhedron
            for i in xrange(len(I)-1):
                polyhedron &= dual_cone_as_polyhedron([alpha[pi[i+1]]-alpha[pi[i]]],
                                                      strict=pi[i] > pi[i+1])

            T = ToricDatum( ring=self.ring, integrand=self.integrand,
                                    cc=self.cc, initials=self.initials,
                                    polyhedron=polyhedron, depth=self._depth )
            T = T.simplify()

            if T.is_empty():
                continue
            T._ordered = True
            yield T

    @cached_simple_method
    def is_regular(self):
        """Test if a balanced toric datum is regular.
        """

        if self.is_empty():
            return True
        if not self.is_balanced():
            return False
        return is_nondegenerate(self.initials, all_subsets=True, all_initial_forms=False,
                                collision_handler=lambda J: setattr(self, '_coll_idx', J))

    def reduce(self, i, j, term_i=None, term_j=None, strict=False):
        """
        For terms term_i and term_j of RHS[i] and RHS[j], respectively, enforce
        term_i || term_j and simplify conditions.
        By default, leading terms are used. If strict is 'True', then strict
        divisibility is enforced.
        We do not require the toric datum to be balanced.
        """

        if i == j:
            raise RuntimeError('I can only reduce pairs of distinct conditions')

        if term_i is None:
            term_i = self.rhs[i].lt() if self.initials[i] is None else self.initials[i].lt()
        else:
            if not is_subpolynomial(self.rhs[i], term_i):
                raise ValueError('Not a term of rhs[i]')
        if term_j is None:
            term_j = self.rhs[j].lt() if self.initials[j] is None else self.initials[j].lt()
        else:
            if not is_subpolynomial(self.rhs[i], term_i):
                raise ValueError('Not a term of rhs[j]')

        lhs_i = self.lhs[i]
        lhs_j = self.lhs[j]

        logger.debug('Reduction: (%d) --> (%d)' % (i,j))
        aa = lhs_j * term_i ; bb = lhs_i * term_j
        gg = gcd(aa,bb); aa //= gg ; bb //= gg
        aa //= aa.lc() ; bb //= bb.lc()

        if strict:
            logger.debug('Enforcing %s || %s (strict divisibility)' % (aa, bb))
        else:
            logger.debug('Enforcing %s || %s ' % (aa,bb))

        polyhedron = self.polyhedron & dual_cone_as_polyhedron([monomial_log(bb) - monomial_log(aa)], strict=strict)

        if polyhedron.dim() == -1:
            logger.debug('Found empty reduction.')
            return ToricDatum( ring=self.ring, integrand=self.integrand,
                                       cc=None, initials=None,
                                       polyhedron=polyhedron, depth=self._depth )


        lhs, rhs, initials = self.lhs[:], self.rhs[:], self.initials[:]

        R = self.ring ;  K = R.fraction_field()

        g = K( self.rhs[j]/self.lhs[j] - term_j/(self.lhs[j] * term_i) * self.rhs[i] )
        lhs[j], rhs[j] = g.denominator(), g.numerator()

        logger.debug('Condition (%d) becomes %s || %s.' % (j, str(lhs[j]), str(rhs[j])))

        if (initials[i] is None) or (initials[j] is None):
            initials[j] = None
        else:
            # Unless the above transformation yields zero on initial forms, we can
            # read off the new one in position j. 
            h = K( self.initials[j]/self.lhs[j] - term_j/(self.lhs[j] * term_i) * self.initials[i] )
            initials[j] = None if h == K(0) else R( h * g.denominator() )

            if not(initials[j] is None) and not is_subpolynomial(rhs[j], initials[j]):
                # If term_i and term_j are INITIAL terms, this can't happen!
                raise RuntimeError('This reduction is not admissible')

            logger.debug('New intial form of (%d) is %s.' % (j, 'undetermined' if initials[j] is None else str(initials[j])))

        return ToricDatum( ring=self.ring, integrand=self.integrand,
                                   cc=zip(lhs,rhs), initials=initials,
                                   polyhedron=polyhedron, depth=self._depth )

    def __str__(self):
        S = 'Toric datum\n'\
            'Base ring: ' + str(self.ring) + '\n\n'\
            'Polyhedron: ' + str(self.polyhedron) + '\n' +\
            str(self.polyhedron.cdd_Hrepresentation()) + '\n'\
            'Integrand: t^(y * ' + str(self.integrand[0]) + ') * q^(y * ' + str(self.integrand[1]) + ')\n'

        if len(self.cc) == 0:
            return S + 'No divisibility conditions.'

        width = max(map(lambda f: len(filter( lambda i: i > 0, f.exponents()[0]) ),self.lhs)) * 4 + 2
        for i in xrange(len(self.cc)):
            if self.initials[i] is None:
                S += ('(%2d )  %'+str(width)+'s  ||  %s\n') % (i, str(self.lhs[i]), str(self.rhs[i]))
            else:
                S += ('(%2d )  %'+str(width)+'s  || <<%s>>') % (i, str(self.lhs[i]), str(self.initials[i]))
                rem = self.rhs[i] - self.initials[i]
                if rem.lc()  > Integer(0):
                    S += ' + ' + str(rem)
                elif rem.lc() < Integer(0):
                    S += ' ' + str(rem)
                S += '\n'
        return S

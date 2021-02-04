from sage.all import *

from convex import RationalSet, dual_cone_as_polyhedron, PositiveOrthant
import util
import toric

import itertools

class LaurentError(Exception):
    pass

from util import create_logger
logger = create_logger(__name__)

class LaurentPolynomial:
    __slots__ = ['ring', 'nvars', 'den', 'num', 'f']

    def __init__(self, f):
        # NOTE: f should belong to a *multivariate* polynomial ring over
        # a field or to its field of fractions.
        f = FractionField(f.parent())(f)
        self.ring = f.parent()
        self.nvars = self.ring.ngens()
        self.den = f.denominator()
        self.num = f.numerator()/self.den.lc()
        self.den //= self.den.lc()
        if not self.den.is_monomial():
            raise LaurentError('not a Laurent polynomial')
        self.f = self.num/self.den

    def decompose(self):
        beta = vector(self.den.exponents()[0])
        return [(c,vector(QQ,alpha)-beta) for c,alpha in zip(self.num.coefficients(), self.num.exponents())]

    def exponents(self):
        return [alpha for _,alpha in self.decompose()]

    def terms(self):
        return [LaurentPolynomial(c*t/self.den) for (c,t) in list(self.num)]

    def is_integer_valued(self, RS=None):
        if RS is None:
            # Test if self.f is an honest polynomial.
            return self.den == 1
        return all(RS.is_contained_in_dual(alpha) for alpha in self.exponents())

    def is_term(self):
        return len(self.exponents()) == 1

    def is_unit(self, RS=None):
        li = self.exponents()
        if len(li) != 1:
            return False
        if RS is None:
            return True
        return RS.is_perpendicular(li[0])

    def divides(self, other):
        try:
            _ = other/self
        except LaurentError:
            return False
        else:
            return True

    def is_subpolynomial(self, other):
        li = other.decompose()
        return all(a in li for a in self.decompose())

    def factor(self):
        return Factorization([(LaurentPolynomial(g),e) for (g,e) in self.f.factor()])

    def __nonzero__(self):
        return bool(self.f)

    def __add__(self, other):
        return LaurentPolynomial(self.f + other.f)

    def __sub__(self, other):
        return LaurentPolynomial(self.f - other.f)

    def __mul__(self, other):
        return LaurentPolynomial(self.f * other.f)

    def __div__(self, other):
        return LaurentPolynomial(self.f / other.f)

    def __pow__(self, exponent):
        return LaurentPolynomial(self.f ** exponent)

    def __eq__(self, other):
        return self.f == other.f

    def __hash__(self):
        return hash(self.f)

    def __str__(self):
        return str(self.f)

    def __repr__(self):
        return repr(self.f)

class LaurentIdeal:
    # Ideals of the rings of RS-integer Laurent polynomials.
    # Detects units, removes zeros and multiples.

    __slots__ = ['ring', 'gens', 'initials', 'RS']

    def __init__(self, gens, initials=None, RS=None, ring=None, normalise=False):
        initials = [None for f in gens] if initials is None else list(initials)

        if not gens and ring is None:
            raise ValueError('need to specify base ring')
        self.ring = ring if ring is not None else gens[0].ring

        if RS is None:
            RS = RationalSet(PositiveOrthant(self.ring.ngens()))

        if RS.ambient_dim != self.ring.ngens():
            raise ValueError('rational set and number of variables are inconsistent')

        if RS.is_empty():
            # Q: is this controversial?
            self.gens = []
            self.initials = []
            self.RS = RS
            return

        # Get rid of zeros, detect units.
        new_gens, new_initials = [], []
        for f, init in zip(gens, initials):
            if not f:
                continue
            if f.is_unit(RS):
                new_gens = [LaurentPolynomial(f.ring(1))]
                new_initials = [LaurentPolynomial(f.ring(1))]
                break
            new_gens.append(f)

            if f.is_term():
                foo = f
            elif init is None:
                foo = None
            else:
                foo = init
            new_initials.append(foo)

        # Now get rid of g whenever g/f is an RS-integer-valued
        # Laurent polynomial.
        def lte(i,j):
            if i == j:
                return True
            try:
                g = new_gens[j]/new_gens[i]
            except LaurentError:
                return False
            return g.is_integer_valued(RS)
        mins = util.minimal_elements(range(len(new_gens)), lte)

        self.gens = [new_gens[i] for i in mins]
        self.initials = [new_initials[i] for i in mins]
        self.RS = RS

        if normalise:
            for i, f in enumerate(self.gens):
                c = LaurentPolynomial(f.ring(f.num.lc()))
                self.gens[i] /= c
                if self.initials[i] is None:
                    continue
                self.initials[i] /= c

        # BEGIN SANITY CHECK
        assert all(
            (self.initials[i] is None) or self.initials[i].is_subpolynomial(self.gens[i])
            for i in xrange(len(self.gens)))
        # END SANITY CHECK

    def __eq__(self, other):
        raise NotImplementedError

    def simplify(self):
        I = LaurentIdeal(gens=self.gens, initials=self.initials, RS=self.RS, ring=self.ring, normalise=True)

        changed = True
        while changed:
            changed = False
            gens = I.gens[:]
            initials = I.initials[:]
            for i,j in itertools.product(range(len(gens)), repeat=2):
                if i == j:
                    continue
                for ti,tj in itertools.product(
                        (gens[i] if initials[i] is None else initials[i]).terms(),
                        (gens[j] if initials[j] is None else initials[j]).terms()):
                    quo = ti/tj
                    if not quo.is_integer_valued(self.RS):
                        continue
                    f = gens[i] - quo*gens[j]
                    if len(f.exponents()) < len(gens[i].exponents()):
                        changed = True
                        gens[i] = f
                        if (initials[i] is not None) and (initials[j] is not None):
                            initials[i] = initials[i] - quo * initials[j]
                            if not initials[i]:
                                initials[i] = None
                        else:
                            initials[i] = None
                        I = LaurentIdeal(gens=gens, initials=initials, RS=I.RS, ring=I.ring, normalise=True)
                        break
                else:
                    continue
                break
        return I

    def reduce(self, i, j, ti, tj, strict):
        # Enforce t_i || t_j and change F.gens[j] in a new Laurent ideal.
        # For balanced polynomials, initial terms should be used.

        if i == j:
            raise ValueError('need distinct indices')
        if not (ti in self.gens[i].terms() and tj in self.gens[j].terms()):
            raise ValueError('not a term of the given specified polynomial')
        if ((self.initials[i] is not None) and (ti not in self.initials[i].terms())) or ((self.initials[j] is not None) and (tj not in self.initials[j].terms())):
            raise ValueError('non-initial term')

        alpha_i = ti.exponents()[0]
        alpha_j = tj.exponents()[0]
        RS = self.RS & RationalSet(dual_cone_as_polyhedron([alpha_j - alpha_i], strict=strict))

        gens = self.gens[:]
        initials = self.initials[:]

        gens[j] = gens[j] - tj/ti * gens[i]
        if (initials[i] is None) or (initials[j] is None):
            initials[j] = None
        else:
            f = initials[j] - tj/ti * initials[i]
            initials[j] = f if f else None
        return LaurentIdeal(gens=gens, initials=initials, RS=RS, ring=self.ring)
        
    def is_balanced(self):
        return not any(init is None for init in self.initials)
    
    def balance(self, strategy='min'):
        # NOTE 1: repeated application might be necessary 
        # NOTE 2: shares code with ToricDatum.balance
        if self.is_balanced():
            yield self
            return
        idx, weights = zip(*[(i, len(self.gens[i].exponents())) for i in range(len(self.gens)) if self.initials[i] is None])
        J = [idx[weights.index(min(weights))]] if strategy == 'min' else idx

        for F, Q in toric.relative_initial_forms([self.gens[j].num for j in J], polyhedron=None):
            new_RS = self.RS & RationalSet(Q)
            if new_RS.is_empty():
                continue
            new_initials = self.initials[:]
            for j,f in zip(J, F):
                new_initials[j] = LaurentPolynomial(f/self.gens[j].den)
            yield LaurentIdeal(gens=self.gens, initials=new_initials, RS=new_RS, ring=self.ring)

    def __str__(self):
        return 'LaurentIdeal(gens=%s, initials=%s)' % (self.gens, self.initials)
    __repr__ = __str__

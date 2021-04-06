"""Cyclotomic rational functions.
"""

from sage.all import (ZZ, QQ, SR, Infinity, FractionField, vector,
                      zero_vector, prod, PolynomialRing, identity_matrix,
                      gcd, divisors, matrix)

import itertools

from collections import Counter

from .util import monomial_log, evaluate_polynomial, unzip, split_vector, common_overring

from .util import create_logger
logger = create_logger(__name__)


class CyclotomicRationalFunction:
    """A cyclotomic rational function is an expression
    Q = f * X^alpha[0]/prod(1-X^alpha[i], i=1,..,k), where alpha[i] in ZZ^n
    and f is a polynomial in X = [X[0], ...].
    """

    __slots__ = ['polynomial', 'ring', 'variables', 'nvars', 'exponents',
                 '_known_to_be_normalised', '_known_to_be_reduced']

    def __init__(self, polynomial, exponents=None,
                 known_to_be_normalised=False,
                 known_to_be_reduced=False):

        # NOTE: polynomial.ring() must be 'multivariate' (even if there's just
        # one variable)

        self.polynomial = polynomial
        self.ring = self.polynomial.parent()
        self.variables = self.ring.gens()
        self.nvars = len(self.variables)

        if (exponents is None) or (polynomial == 0):
            self.exponents = [zero_vector(ZZ, self.nvars)]
            known_to_be_normalised = True
        else:
            self.exponents = [vector(ZZ, e) for e in exponents]

        self.exponents = [self.exponents[0]] + sorted(self.exponents[1:])

        if 0 in self.exponents[1:]:
            raise TypeError('Only non-zero vectors can be used as exponents for the denominator')

        if any(len(e) != self.nvars for e in self.exponents):
            raise TypeError('Exponent vector and number number of variables do not match')

        self._known_to_be_normalised = known_to_be_normalised
        self._known_to_be_reduced = known_to_be_reduced

    def copy(self):
        return CyclotomicRationalFunction(self.polynomial, self.exponents,
                                          self._known_to_be_normalised,
                                          self._known_to_be_reduced)

    def __bool__(self):
        return bool(self.polynomial)

    __nonzero__ = __bool__

    def degree(self, i=0):
        if not self.polynomial:
            return -Infinity
        x = self.variables[i]
        return self.polynomial.degree(x) + self.exponents[0][i] - sum(max(0, a[i]) for a in self.exponents[1:])

    def is_compatible_with(self, Q):
        # Check if we can add these two.
        return self.ring == Q.ring

    def evaluate(self, variables=None):
        if variables is None:
            R = self.ring
            K = FractionField(R)

            if not self.polynomial:
                return K.zero()

            variables = [K.coerce(x) for x in self.variables]
            exp = lambda v: K.prod(x**e for (x, e) in zip(variables, v))
            return K.product(
                evaluate_polynomial(self.polynomial, variables),
                exp(self.exponents[0]) / K.prod(K.one()-exp(e) for e in self.exponents[1:])
                )

        if variables == 'symbolic':
            variables = [SR(str(v)) for v in self.variables]
            coerc = lambda x: SR(x)
        else:
            coerc = lambda x: x

        exp = lambda v: prod(variables[i] ** v[i] for i in range(self.nvars))
        return coerc(
            evaluate_polynomial(self.polynomial, variables) *
            exp(self.exponents[0]) / prod(1-exp(e) for e in self.exponents[1:])
            )

    def evaluate_reciprocal(self):
        """Return 1/self.evaluate() assuming that it is a polynomial, that
        self.polynomial is constant, and that self.exponents[0] contains
        non-positive entries only.
        """

        if not self.polynomial.is_constant() or not self.polynomial:
            raise ValueError('polynomial is not a non-zero constant')

        R = self.ring
        exp = lambda v: R.prod(self.variables[i] ** v[i] for i in range(self.nvars))

        y, z = split_vector(self.exponents[0])
        if y:
            raise ValueError('not a polynomial')

        res = R.one()
        for c in self.exponents[1:]:
            a, b = split_vector(c)
            z -= b
            res = R.product(res, exp(b) - exp(a))

        if any(e < 0 for e in z):
            raise ValueError('not a polynomial')

        Q = R.base_ring()
        return R.prod([R.coerce(Q.one()/Q(self.polynomial)), exp(z), res])

    def triangulate(self):
        """Produce a generator yielding 'simplicial' cyclotomic rational
        functions (-> polynomials are constant) that sum up to 'self'.
        """
        coeff = self.polynomial.coefficients()
        mon = self.polynomial.monomials()

        for i in range(len(mon)):
            exps = self.exponents[:]
            exps[0] += monomial_log(mon[i])
            yield CyclotomicRationalFunction(self.ring(coeff[i]), exps).normalise()

    def __str__(self):
        return str(self.evaluate())

    def normalise(self):
        # 'self' is normalised iff
        # (1) the first non-zero entry in each ray in the denominator is positive and
        # (2) gcd(self.polynomial) == 1; over SR, ignore (2).

        if self._known_to_be_normalised or not self:
            return self

        f = self.polynomial
        alpha = self.exponents[:]
        k = len(alpha)-1

        for i in range(1, k+1): # we use f * X^u/(1-X^v) == (-f) * X^(u-v)/(1-X^(-v))
            if next(b for b in alpha[i] if b != 0) < 0:
                alpha[i] = -alpha[i]
                f = -f
                alpha[0] += alpha[i]

        try:
            g = gcd(f.monomials())
        except (AttributeError, NotImplementedError):
            # This doesn't currently work for polynomials over functions fields.
            pass
        else:
            f //= g
            alpha[0] += monomial_log(g)

        # NOTE: normalising a reduced rational function produces another
        # reduced one.
        return CyclotomicRationalFunction(
            f, exponents=alpha,
            known_to_be_normalised=True,
            known_to_be_reduced=self._known_to_be_reduced)

    def reduce(self):
        """Cancel factors in the denominator.
        """

        if self.ring.base_ring() == SR:
            return self  # again, few things work in the symbolic case
        elif self._known_to_be_reduced:
            return self
        elif self.polynomial.is_constant():
            Q = self.copy()
            Q._known_to_be_reduced = True
            return Q

        f = self.polynomial
        alpha = self.exponents[:]
        k = len(alpha)-1

        exp = lambda v: self.ring.prod(self.variables[i] ** v[i] for i in range(self.nvars)) # only non-negative entries allowed here!

        for i in range(1, k + 1):
            beta = alpha[i]

            # (1) Check if we can cancel all of 1-X^beta.
            # We use f/(1-X^beta) = X^(beta^-)*f/(X^(beta^-)-X(^beta^+)
            # to translate between polynomials and Laurent polynomials.

            beta_pos, beta_neg = split_vector(beta)
            g = exp(beta_neg) - exp(beta_pos)
            if g.divides(f):
                f //= g
                alpha[0] += beta_neg
                alpha[i] = None
                continue

            # (2) Check if we can replace 1-X^beta by some proper divisor.
            e = gcd(beta)
            e = -e if e < 0 else e # NOTE: the documentation of Sage doesn't seem to guarantee non-negativity of GCDs
            if e == 1:
                continue

            gamma = beta / e

            for d in divisors(e):
                if d == e:
                    break

                delta = d * gamma
                m = e // d
                assert beta == m * delta

                delta_pos, delta_neg = split_vector(delta)
                y = exp(delta_pos)/exp(delta_neg) # == exp(delta)

                g = (self.ring)(exp((m-1) * delta_neg) * sum(y ** i for i in range(m)))

                # (1-X^beta)/(1-X^delta) = 1 + X^delta + ... + X^((m-1)*delta)
                #                        = X^(-(m-1)*delta^-) * g
                # Hence:
                # f/(1-X^beta) = (f/g) * X^((m-1)*delta^-) / (1-X^delta)

                if not g.divides(f):
                    continue

                f //= g
                alpha[i] = delta
                alpha[0] += (m-1) * delta_neg
                break

        return CyclotomicRationalFunction(
            f, exponents=[alpha[0]] + [a for a in alpha[1:] if a is not None],
            known_to_be_reduced=True)  # NOTE: The output need not be normalised.

    def simplify(self):
        return self.reduce().normalise()

    @staticmethod
    def common_denominator(it):
        """Construct a cyclotomic rational function 'cr' such that 'self'
        can be written as f * cr for a (non-Laurent) polynomial f.
        """

        a = None
        D = {}
        ring = None

        for cr in it:
            if ring is None:
                ring = cr.ring

            _, b = split_vector(cr.exponents[0])
            a = b if a is None else vector(ZZ, [max(x) for x in zip(a,b)])

            E = Counter([tuple(v) for v in cr.exponents[1:]])
            for v, m in E.items():
                D[v] = max(D[v],m) if v in D else m

        if a is None or ring is None:
            raise RuntimeError('need a non-empty iterable')

        exps = []
        for v, m in D.items():
            exps.extend([v] * m)
            _, vneg = split_vector(v)
            a += m * vneg

        return CyclotomicRationalFunction(ring.one(), [-a] + exps) # .normalise()

    def __neg__(self):
        Q = self.copy()
        Q.polynomial = -Q.polynomial
        return Q

    def __add__(self, other):
        if self.nvars != other.nvars:
            raise ValueError('inconsistent numbers of variables')

        ring = common_overring(self.ring, other.ring)

        if self.ring.variable_names() != other.ring.variable_names():
            raise ValueError('inconsistent variable names')

        if self.exponents[1:] == other.exponents[1:]:
            K = FractionField(ring)
            variables = [K.coerce(x) for x in self.variables]

            exp = lambda v: K.prod(variables[i] ** v[i] for i in range(self.nvars))
            return CyclotomicRationalFunction.from_laurent_polynomial(
                exp(self.exponents[0]) * K.coerce(self.polynomial) + exp(other.exponents[0]) * K.coerce(other.polynomial),
                ring,
                exponents=[vector(ZZ,self.ring.ngens())] + self.exponents[1:])
        elif not self:
            return other
        elif not other:
            return self

        Q = self.normalise()
        other = other.normalise()

        alpha = Q.exponents
        alpha_pos, alpha_neg = unzip(split_vector(v) for v in alpha)

        beta = other.exponents
        beta_pos, beta_neg = unzip(split_vector(w) for w in beta)

        k = len(alpha) - 1
        ell = len(beta) - 1

        I = list(range(1, k + 1))
        J = list(range(1, ell + 1))
        for i in range(1, k + 1):
            j = next((j for j in J if alpha[i] == beta[j]), None)
            if j is not None:
                I.remove(i)
                J.remove(j)

        # Now I and J contain unmatched indices so the sum is given by
        #
        # X^alpha[0] * prod(1-X^beta[j], j in J) * f + X^beta[0] * prod(1-X^alpha[i], i in I) * g
        # ---------------------------------------------------------------------------------------
        # prod(1-X^alpha[i], i=1,..k) * prod(1-X^beta[j], j in J)
        #

        # Multiplying the numerator by exp(v+w) yields a polynomial.
        v = alpha_neg[0] + sum(beta_neg[j] for j in J)
        w = beta_neg[0] + sum(alpha_neg[i] for i in I)

        exp = lambda v: ring.prod(self.variables[i] ** v[i] for i in range(self.nvars))
        h = ring.summation(
            ring.prod( [ exp(w), exp(alpha_pos[0]) ] + [ exp(beta_neg[j])  -  exp(beta_pos[j]) for j in J ] + [ Q.polynomial ] ),
            ring.prod( [ exp(v), exp(beta_pos[0]) ] + [ exp(alpha_neg[i]) - exp(alpha_pos[i]) for i in I ] + [ other.polynomial ] )
            )
        exponents = [-v-w] + alpha[1:] + [beta[j] for j in J]
        return CyclotomicRationalFunction(h, exponents).normalise()

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if self.nvars != other.nvars:
            raise ValueError('inconsistent numbers of variables')
        if self.ring.variable_names() != other.ring.variable_names():
            raise ValueError('inconsistent variable names')
        ring = common_overring(self.ring, other.ring)

        return CyclotomicRationalFunction(
            ring.product(ring(self.polynomial), ring(other.polynomial)),
            [self.exponents[0] + other.exponents[0]] +
             self.exponents[1:] + other.exponents[1:]
            )

    def monomial_substitution(self, new_ring, Phi):
        """
        Perform a monomial substitution (assumed to be valid) of variables.

        'new_ring' should be a polynomial ring in, say, 'm' variables z_0, ...
        Let 'n' be the number of variables x_0, ... of 'self'.
        'Phi' should be an n by m matrix over ZZ, the rows of
        which encode the substitution x_i |--> z^Phi[i].
        """

        Phi = matrix(ZZ, Phi)
        m = new_ring.ngens()
        if (self.nvars != Phi.nrows()) or (m != Phi.ncols()):
            raise TypeError('The substitution matrix has the wrong size')

        # The rule x_i |--> z^Phi[i] yields x^a |--> z^(a * Phi).
        beta = [a * Phi for a in self.exponents]
        if 0 in beta[1:]:
            raise ZeroDivisionError('Invalid monomial substitution')

        K = FractionField(new_ring)
        new_variables = [K.coerce(x) for x in new_ring.gens()]
        exp = lambda a: K.prod(x ** e for (x,e) in zip(new_variables,a))
        h = evaluate_polynomial(self.polynomial, [exp(v) for v in Phi])
        return CyclotomicRationalFunction.from_laurent_polynomial(h, new_ring, exponents=beta)

    @classmethod
    def from_laurent_polynomial(cls, f, ring, exponents=None):
        # NOTE:
        # We currently use rational functions instead of either Sage's
        # built-in Laurent polynomials or those from laurent.py.

        K = FractionField(ring)
        variables = [K.coerce(x) for x in ring.gens()]

        if exponents is None:
            exponents = [vector(ZZ, len(variables))]

        try:
            f = K(f)
        except TypeError:
            raise TypeError('Not a rational function over the given ring')

        den = f.denominator()
        lc = den.lc()
        num = f.numerator() / lc
        den = den / lc
        assert num == ring(num)
        assert (den == 1) or den.is_monomial()
        try:
            return cls(num, [-monomial_log(den) + exponents[0]] + exponents[1:])
        except TypeError:
            raise TypeError('Not a Laurent polynomial')

    @classmethod
    def from_split_expression(cls, g, y, ring):
        # Suppose 'g' is a symbolic expression in the variables 'y' such
        # that the denominator of 'g' splits into linear factors 1-y[i].
        # Turn 'g' into a cyclotomic rational function over 'ring'.
        # Here, y[i] will be turned into ring.gens()[i]

        num = g.numerator()
        r = len(y)
        e = identity_matrix(QQ, r)

        exponents = [zero_vector(len(y))]

        # Unpack the denominator with multiplicities.
        for pol in itertools.chain.from_iterable([a] * int(i) for (a, i) in g.denominator().factor_list()):
            # Look for 'pol + 1' in y. If it isn't there, then 'pol' should be a constant.
            i = next((i for i in range(r) if y[i] == pol + 1), None)
            if i is None:
                # Move constants into the numerator
                if not ((PolynomialRing(QQ,y))(pol)).is_constant():
                    raise TypeError('Cannot handle this expression')
                num /= pol
            else:
                num = -num # Encode (y[i]-1) as (-1) * (1-y[i]).
                exponents.append(e[i])

        return cls.from_laurent_polynomial(num({a: ring.gen(i) for i, a in enumerate(y)}), ring, exponents=exponents)

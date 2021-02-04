from sage.all import matrix, PolynomialRing, identity_matrix, QQ, vector, FractionField, SR

from .util import create_logger, cached_simple_method

from .reps import IgusaDatum, RepresentationProcessor
from .convex import PositiveOrthant, RationalSet
from .util import evaluate_matrix
from .laurent import LaurentIdeal, LaurentPolynomial
from .abstract import LocalZetaProcessor


logger = create_logger(__name__)


def bullet_dual(A):
    R = A.base_ring()
    S = PolynomialRing(QQ, 'z', A.ncols())

    def fun(v):
        return sum(a * x for (a, x) in zip(v, S.gens()))
    I = identity_matrix(S, A.nrows())
    J = identity_matrix(S, R.ngens())
    return matrix(S, [[fun(e * A(*f.list())) for f in J] for e in I])


def circ_dual(A):
    R = A.base_ring()
    S = PolynomialRing(QQ, 'x', A.nrows())
    xx = vector(S, S.gens())
    basis = [evaluate_matrix(A, y) for y in identity_matrix(QQ, R.ngens())]
    return matrix(S, [xx * matrix(S, A) for A in basis])


class AskProcessor(RepresentationProcessor):
    def __init__(self, arg, mode=None):
        if mode is None:
            mode = 'O'

        if mode not in ['O', 'K', 'BO', 'BK', 'TO', 'TK']:
            raise ValueError("invalid mode")

        self.translation = SR('q')**(arg.nrows() - arg.ncols()) if 'T' in mode else None
        self.R = arg
        for x in mode[:-1]:
            if x == 'B':
                self.R = bullet_dual(self.R)
            elif x == 'T':
                self.R = self.R.transpose()
            else:
                raise ValueError

        self.d = self.R.nrows()
        self.e = self.R.ncols()

        self.mode = mode[-1]
        self.ring = self.R.base_ring()
        self.ell = self.ring.ngens()

        self.basis = [evaluate_matrix(self.R, y) for y in identity_matrix(QQ, self.ell)]
        # V = (QQ**(self.d * self.e)).subspace([A.list() for A in self.basis])
        # if V.dimension() != self.ell:
        #     raise ValueError('subspace parameterised by matrix of linear forms has wrong dimension')

    def padically_evaluate_regular(self, datum):
        # The essential change from representation zeta functions is that
        # the extra variable may be a unit here.
        for z in super(AskProcessor, self).padically_evaluate_regular(datum, extra_RS=RationalSet(PositiveOrthant(1))):
            yield z

    def topologically_evaluate_regular(self, datum):
        raise NotImplementedError

    @cached_simple_method
    def root(self):
        if self.mode == 'K':
            ell = self.ell
            self.RS = RationalSet([PositiveOrthant(ell)], ambient_dim=ell)

            actual_ring = self.ring
            F = FractionField(actual_ring)
            r = matrix(F, self.R).rank()
            self.r = r
            if not self.d:
                return

            F = [
                LaurentIdeal(
                    gens=[LaurentPolynomial(f) for f in self.R.minors(j)],
                    RS=self.RS,
                    normalise=True)
                for j in range(r + 1)
            ]
        elif self.mode == 'O':
            self.RS = RationalSet([PositiveOrthant(self.d)], ambient_dim=self.d)
            actual_ring = PolynomialRing(QQ, 'x', self.d)
            xx = vector(actual_ring, actual_ring.gens())
            self.C = matrix(actual_ring, [xx * matrix(actual_ring, A) for A in self.basis])
            r = matrix(FractionField(actual_ring), self.C).rank()
            self.r = r
            if not self.d:
                return
            F = [LaurentIdeal(gens=[LaurentPolynomial(f)
                                    for f in self.C.minors(j)],
                              RS=self.RS,
                              normalise=True)
                 for j in range(r + 1)]
        else:
            raise ValueError('invalid mode')

        oo = r + 1

        # On pairs:
        # The first component is used as is, the second is multiplied by the extra
        # variable. Note that index 0 corresponds to {1} and index oo to {0}.
        self.pairs = ([(oo, 0)] +
                      [(i, oo) for i in range(1, r)] +
                      [(i, i - 1) for i in range(1, r + 1)])
        # Total number of pairs: 2 * r
        self.integrand = ((1,) + (2 * r - 1) * (0,),
                          (self.d - r + 1,) + (r - 1) * (-1,) + r * (+1,))
        self.datum = IgusaDatum(F + [LaurentIdeal(gens=[], RS=self.RS, ring=FractionField(actual_ring))]).simplify()
        return self.datum

    def padically_evaluate(self, shuffle=False):
        if self.root() is None:
            return SR(1)
        r = ((1 - SR('q')**(-1))**(-1) * LocalZetaProcessor.padically_evaluate(self, shuffle=shuffle)).factor()
        return r if self.translation is None else r(t=self.translation * SR('t')).factor()

    def __repr__(self):
        if self.root() is not None:
            s = 'Ask processor:\n'
            s += 'Base ring: %s\n' % self.datum.ring
            s += 'R =\n' + str(self.R) + '\n'
            s += 'd = %d\n' % self.d
            s += 'e = %d\n' % self.e
            s += 'r = %d\n' % self.r
            s += 'Root:\n%s\n' % self.datum
            s += 'Pairs: ' + str(self.pairs) + '\n'
            s += 'Integrand: ' + str(self.integrand)
            return s
        else:
            return 'Trivial ask processor'

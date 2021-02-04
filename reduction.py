from sage.all import *
import itertools
from util import normalise_poly, terms_of_polynomial

BALANCE_FULL_BOUND = 10
DEPTH_BOUND = 24

from util import create_logger
logger = create_logger(__name__)

class ReductionError(Exception):
    pass

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

def Reductor(strategy):
    def red(unprocessed, regular):
        good = Integer(0)
        while unprocessed:

            T = unprocessed.pop()
            logger.info('POP [#unprocessed = %2d, #regular = %d]' % (len(unprocessed)+1,len(regular)))

            T = T.simplify()

            if T.is_empty():
                continue

            if T.is_regular():
                good += 1
                regular.append(T)
                continue
            
            # Try to apply `preemptive reduction', i.e. reduce
            # a possibly unbalanced toric datum.
            try:
                chops = strategy.prechopper(T, range(len(T.rhs)))
            except ReductionError:
                pass
            else:
                unprocessed.extend(t for t in chops if not t.is_empty())
                logger.info('Preemptive reduction performed.')
                continue

            if not T.is_balanced():
                logger.info('Balancing...')
                balancing_strategy = 'full' if T.weight() < BALANCE_FULL_BOUND else 'min'
                
                cnt = 0
                for t in T.balance(strategy=balancing_strategy):
                    if t.is_empty():
                        continue
                    unprocessed.append(t)
                    cnt += 1
                logger.info('Pushed %d balanced cases.' % cnt)
                continue

            if strategy.order and not T.is_ordered():
                logger.info('Ordering...')
                cnt = 0
                for t in T.order():
                    if t.is_empty():
                        continue
                    unprocessed.append(t)
                    cnt += 1
                logger.info('Pushed %d ordered cases.' % cnt)
                continue

            # Try to apply reduction to a balanced but singular toric datum.
            try:
                chops = strategy.chopper(T, T._coll_idx)
            except ReductionError, e:
                logger.debug("Don't know how to reduce this.")
                raise e
            else:
                zoo = [t for t in chops if not t.is_empty()]
                unprocessed.extend(zoo)
                logger.info('Pushed %d new cases.' % len(zoo))
        logger.info('Total number of regular toric data: %d' % len(regular))
        return
    return red

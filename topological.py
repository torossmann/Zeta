"""Evaluation of toric cone integrals.
"""

from sage.all import *

from convex import conify_polyhedron, StrictlyPositiveOrthant, DirectProductOfPolyhedra

from torus import SubvarietyOfTorus

import common

import surf

from surf import SURF, SURFSum

from triangulate import triangulate_cone

from tmplist import TemporaryList

from util import TemporaryDirectory, readable_filesize

from contextlib import closing

from util import create_logger
logger = create_logger(__name__)

def _topologise_scone(sc, Phi):
    if not sc.rays:
        raise ValueError('Cannot handle empty scones')
    if (Phi.nrows() != len(sc.rays[0])) or (Phi.ncols() != 2):
        raise ValueError('Invalid substitution matrix')

    li = [(int(Phi.column(0)*vector(ZZ,v)),
           int(Phi.column(1)*vector(ZZ,v))) for v in sc.rays]

    # An element of 'li' of the form (0,b) is really just the
    # scalar -b in disguise (mind the sign!).
    # Collect all of those together, cancelling common factors
    # with the numerator sc.multiplicity.

    rays = []
    num, den = sc.multiplicity, 1
    for (a,b) in li: # this becomes 1/(a*s-b) in the SURF
        if a == 0:
            den *= (-b)
        else:
            rays.append((a,b))
    g = int(gcd(sc.multiplicity, den))
    num /= g
    den /= g

    if den == -1:
        num, den = -num, 1

    if den != 1:
        rays.append((0,-den))
    return SURF(scalar=num, rays=rays)

def topologise_cone(C, Phi):
    """
    Turn the cone 'C' into a generator of SURFs via the substitution matrix
    'Phi'.
    """
    return (_topologise_scone(sc, Phi) for sc in triangulate_cone(C))

def evaluate_regular(T, surfsum):
    """
    Evaluate a single regular toric datum topologically.
    """

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
            surfsum.add(SURF(scalar=chi*S.scalar, rays=S.rays))

def multicrunch(surfsums, varname=None):
    """
    Given an iterable consisting of SURFSum, compute the rational function
    given by their combined sum.
    """
    
    surfsums = list(surfsums)

    #
    # Combine the various critical sets and construct a candidate denominator.
    #

    critical = set().union(*(Q._critical for Q in surfsums))
    cand = dict()
    for Q in surfsums:
        E = Q._cand
        for r in E.keys():
            if not cand.has_key(r) or cand[r] < E[r]:
                cand[r] = E[r]

    if varname is None:
        varname = 's'

    R = QQ[varname]
    s = R.gen(0)
    g = R(prod((a*s-b)**e for ((a,b),e) in cand.iteritems()))
    m = g.degree()

    logger.info('Total number of SURFs: %d' % sum(Q._count for Q in surfsums))

    for Q in surfsums:
        Q._file.flush()

    logger.info('Combined size of data files: %s' %
         readable_filesize(sum(os.path.getsize(Q._filename) for Q in surfsums))
         )
    logger.info('Number of critical points: %d' % len(critical))
    logger.info('Degree of candidate denominator: %d' % m)

    #
    # Construct m + 1 non-critical points for evaluation.
    #

    values = set()
    while len(values) < m + 1:
        x = QQ.random_element()
        if x in critical:
            continue
        values.add(x)
    values = list(values)

    #
    # Set up parallel computations.
    #

    bucket_size = ceil(float(len(values))/common.ncpus)

    dat_filenames = [Q._filename for Q in surfsums]

    res_names = []
    val_names = []

    value_batches = [values[j::common.ncpus] for j in xrange(common.ncpus)]

    with TemporaryDirectory() as tmpdir:
        for j,v in enumerate(value_batches):
            if not v:
                break

            val_filename = os.path.join(tmpdir, 'values%d' % j)
            val_names.append(val_filename)
            res_names.append(os.path.join(tmpdir, 'results%d' % j))
            with open(val_filename, 'w') as val_file:
                val_file.write(str(len(v)) + '\n')
                for x in v:
                    val_file.write(str(x) + '\n')

        def fun(k):
            ret = surf.crunch(['crunch', val_names[k], res_names[k]]+dat_filenames)
            if ret == 0:
                logger.info('Cruncher #%d finished.' % k)
            return ret

        fun = sage.parallel.decorate.parallel(ncpus=len(res_names))(fun)
        logger.info('Launching %d crunchers.' % len(res_names))

        for (arg, ret) in fun(range(len(res_names))):
            if ret == 'NO DATA':
                raise RuntimeError('A parallel process died')
            if ret != 0:
                raise RuntimeError('crunch failed')

        #
        # Collect results
        #
        pairs = []

        for j,rn in enumerate(res_names):
            it_batch = iter(value_batches[j])
            with open(rn, 'r') as res_file:
                for line in res_file:
                    # We also need to evaluate the candidate denominator 'g'
                    # from above at the given random points.
                    x = QQ(next(it_batch))
                    pairs.append((x, g(x)*QQ(line)))
            
    if len(values) != len(pairs):
        raise RuntimeError('Length of results is off') 

    f = R.lagrange_polynomial(list(pairs))
    res = SR(f/g)
    return res.factor() if res else res

def evaluate(T, red):
    """
    Try to compute the topological zeta function associated with a
    toric datum. In the globally non-degenerate case, success is
    guaranteed.
    """

    

    #
    # STEP 1: reduction
    #
    with TemporaryList() as res:
        with TemporaryList() as stack:
            stack.append(T)
            logger.info('Beginning main loop.')
            red(stack, res)
            logger.info('Main loop finished.')

        #
        # STEP 2: evaluation
        #

        with TemporaryDirectory() as evaldir:
            surfsum_names = [os.path.join(evaldir, 'surfsum%d' % k) for k in xrange(common.ncpus)]

            def fun(k):
                with closing(SURFSum(surfsum_names[k])) as Q:
                    for i in xrange(k, len(res), common.ncpus):
                        evaluate_regular(res[i], Q)
                logger.info('Evaluator #%d finished.' % k)

            ET = sage.parallel.decorate.parallel(p_iter='reference' if common.debug else 'fork', ncpus=common.ncpus)(fun)
            logger.info('Launching %d evaluators.' % common.ncpus)
            for (arg, ret) in ET(range(common.ncpus)):
                if ret == 'NO DATA':
                    raise RuntimeError('A parallel process died.')
            logger.info('All evaluators finished.')

            #
            # STEP 3: Crunch.
            #
            surfsums = []
            try:
                surfsums = [SURFSum(name) for name in surfsum_names]
                return multicrunch(surfsums)
            finally:
                for Q in surfsums:
                    Q.close()

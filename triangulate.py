"""
Triangulations of pointed cones; includes yet another interface to Normaliz.
"""

from sage.all import *

import common
from collections import namedtuple
from shutil import rmtree

import string, subprocess, os

from util import TemporaryDirectory, cd, my_find_executable

from tmplist import TemporaryList

from util import create_logger
logger = create_logger(__name__)

common.normaliz = my_find_executable('normaliz')

# A simplicial cone 'sc' can be turned into an honest one
# via Cone(rays=sc.rays, lattice=ZZ**ambdim, check=False)).

SCONE = namedtuple('SCONE', ['rays', 'multiplicity'])
from surf import SURF

def _explode_vector(v):
    if len(v) == 0:
        return ''
    elif len(v) == 1:
        return str(v[0])
    else:
        return string.join(
            '%d' % a for a in v[:-1]
            ) + ' ' + str(v[-1])

def _normalize_cone(C):
    # Produce valid normaliz input from cone. Please note the fabulous pun!
    s = '%d\n%d\n' % (C.nrays(), C.lattice_dim())
    for r in C.rays():
        s += _explode_vector(r) + '\n'
    return s + 'integral_closure\n'

def _triangulate_cone_internal(C):
    rays = list(C.rays())
    if any(a < 0 for r in rays for a in r):
        raise ValueError('Internal triangulation only implemented for non-negative cones.')
    normalised_rays = [Integer(1)/v.norm(1) * vector(QQ,v) for v in rays]
    for indices in PointConfiguration(normalised_rays).triangulate() if len(normalised_rays) > 1 else [[0]]:
        subrays = [rays[i] for i in indices]
        multiplicity = prod(a for a in matrix(ZZ,subrays).elementary_divisors() if a != 0)
        yield SCONE(rays=subrays, multiplicity=multiplicity)

def _triangulate_cone_normaliz(C):
    with TemporaryDirectory() as tmpdir:
        logger.debug('Temporary directory of this normaliz session: %s' % tmpdir)

        play = os.path.join(tmpdir, 'play')
        with open(play + '.in', 'w') as f:
            f.write(_normalize_cone(C))

        with cd(tmpdir), open('/dev/null', 'w') as DEVNULL:
            retcode = subprocess.call(
                [common.normaliz, '-B', '-t', '-T', '-x=1', play], # -c
                stdout=DEVNULL, stderr=DEVNULL
                )
        if retcode != 0:
            raise RuntimeError('Normaliz failed')

        # Recover all the rays from the triangulation
        with TemporaryList() as rays:
            with open(play+'.tgn', 'r') as f:
                nrays = int(f.readline())
                ambdim = int(f.readline())
                rays = []
                if ambdim != C.lattice_dim():
                    raise RuntimeError('The triangulation lives in the wrong space')
                for line in f:
                    rays.append([int(w) for w in line.split()])
        
                if len(rays) != nrays:
                    raise RuntimeError('Number of rays is off')
                logger.info('Total number of rays in triangulation: %d' % nrays)

            # Recover the simplicial pieces
            cnt = 0
            with open(play+'.tri', 'r') as f:
                ncones = int(f.readline())
                mplus1 = int(f.readline())

                if mplus1 != C.dim() + 1:
                    raise RuntimeError('.tri and .tgn files do not match')
                for line in f:
                    cnt += 1
                    li = [int(w) for w in line.split()]
                    if li[-1] == -1:
                        raise RuntimeError('Multiplicity is missing from Normaliz output')
                    yield SCONE(rays = [rays[i-1] for i in li[:-1]],
                                multiplicity = li[-1]
                                )
        logger.info('Total number of cones in triangulation: %d' % cnt)
        if cnt != ncones:
            raise RuntimeError('Number of simplicial cones is off')

def triangulate_cone(C):
    return _triangulate_cone_normaliz(C) if common.normaliz else _triangulate_cone_internal(C)

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

    if C.dim() == 0:
        raise RuntimeError
        # return iter([])
    else:
        return (_topologise_scone(sc, Phi) for sc in triangulate_cone(C))

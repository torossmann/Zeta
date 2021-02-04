#
# Zeta.
#
# Copyright 2014, 2015, 2016, 2017, 2019 Tobias Rossmann.
#
# This package is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by the
# Free Software Foundation, either version 3 of the License, or (at your
# option) any later version.
#
# This software is distributed in the hope that it will be useful,
# but without any warranty; without even the implied warranty of
# merchantability or fitness for a particular purpose.
# See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with
# this software; if not, see <http://www.gnu.org/licenses>.
#

__version__ = '0.4'
__date__ = 'August 2019'

print 'Loading...'

import common

import addmany

import examples
from subobjects import SubobjectZetaProcessor
from reps import RepresentationProcessor

from ask import AskProcessor
from cico import CicoProcessor, IncidenceProcessor

from algebra import Algebra, Subalgebra
from abstract import ReductionError
from toric import ToricDatum
from util import create_logger, E
from common import symbolic_count_varieties

import surf, smurf
import abstract
import subobjects
import reps
import ask
import util
import cycrat
import triangulate

from laurent import LaurentPolynomial

from subobjects import Strategy

from sage.all import Infinity, var, Matrix, Graph
import sage

from functools import partial

common.VERSION = __version__

logger = create_logger(__name__)

from reps import IgusaProcessor

# The following is supposed to detect a bug which is present (at least)
# in version 7.5.1 and 7.6 of Sage.
__SERIES_BUG = False
def __check_sage_bugs():
    x,y,z = var('x y z')
    if y.series(x) != (z.series(x))(z=y):
        __SERIES_BUG = True

__check_sage_bugs()

class Profile:
    SAVE_MEMORY = 1
    NORMAL = 2
    SPEED = 3

def lookup(entry=None, what=None, type='topological'):
    if entry is None:
        return [(i, examples.names[i][:]) for i, _ in enumerate(examples.algebras)]

    i = examples.id.get(entry)
    if i is None:
        try:
            i = int(entry)
        except ValueError:
            raise KeyError('Unknown algebra')
    if i < 0 or i >= len(examples.algebras):
        raise KeyError('Invalid index')

    if what is None:
        return examples.algebras[i]
    elif what == 'id':
        return i
    elif what == 'names':
        return examples.names[i]

    if type == 'topological':
        D = examples.topzetas
    elif type in ['p-adic', 'local']:
        D = examples.padzetas
    else:
        raise ValueError('unknown type')
    return D[i].get(what, None)

def zeta_function(type, L, objects=None, optimise_basis=False,
                  ncpus=None, alt_ncpus=None, strategy=None, profile=None, verbose=False,
                  optlevel=None, addmany_dispatcher=None, mode=None,
                  debug=None, **kwargs):

    if type not in ['p-adic', 'topological']:
        raise ValueError('Unknown type of zeta function')

    if type == 'p-adic':
        if common.count is None:
            raise RuntimeError('LattE/count is required in order to compute p-adic zeta functions')
        elif __SERIES_BUG:
            raise RuntimeError('power series expansions in this version of Sage cannot be trusted')

    # Multiprocessing.
    if ncpus is None:
        ncpus = Infinity
    from multiprocessing import cpu_count
    common.ncpus = min(ncpus, cpu_count())

    if alt_ncpus is None:
        alt_ncpus = common.ncpus
    common._alt_ncpus = alt_ncpus

    if addmany_dispatcher is None:
        addmany_dispatcher = 'numerator'
    common.addmany_dispatcher = addmany_dispatcher

    common.debug = False if debug is None else debug

    if optlevel is None:
        optlevel = 1
    common.optimisation_level = optlevel

    # Reduction strategies.
    if strategy is None:
        strategy = Strategy.NORMAL

    # Memory profiles.
    if profile is None:
        profile = Profile.NORMAL
    if profile not in [Profile.SAVE_MEMORY, Profile.NORMAL, Profile.SPEED]:
        raise ValueError('Invalid profile')
    if profile == Profile.SAVE_MEMORY:
        common.save_memory = True
        common.plumber = True
    elif profile == Profile.NORMAL:
        common.save_memory = False
        common.plumber = True
    elif profile == Profile.SPEED:
        common.save_memory = False
        common.plumber = False

    if verbose:
        from logging import INFO, DEBUG
        loglevels = [(logger, INFO), (smurf.logger, INFO), (surf.logger, INFO),
                     (torus.logger, INFO), (abstract.logger, DEBUG),
                     (cycrat.logger, INFO), (triangulate.logger, INFO),
                     (reps.logger, INFO), (subobjects.logger, INFO),
                     (ask.logger, INFO), (cico.logger, DEBUG),
                     (addmany.logger, INFO), ]
        oldlevels = []

        for m,level in loglevels:
            old = m.getEffectiveLevel()
            oldlevels.append(old)
            m.setLevel(min(old,level))

    if util.is_graph(L):
        if L.has_multiple_edges():
            raise ValueError('parallel edges not supported')
        
    if (util.is_matrix(L) or util.is_graph(L)) and objects not in ['ask', 'cico', 'adj', 'inc']:
        raise ValueError('invalid objects specified for given input')
    
    elif util.is_polynomial(L):
        # Turn a polynomial into a list of polynomials.
        L = [L]
    elif util.is_string(L):
        L = lookup(L)
        
    if objects in ['poly', 'igusa']:
        proc = IgusaProcessor(*L)
    elif objects in ['subalgebras', 'ideals']:
        proc = SubobjectZetaProcessor(L, objects, strategy=strategy)
    elif objects == 'reps':
        proc = RepresentationProcessor(L)
    elif objects == 'ask':
        if util.is_graph(L):
            signs = kwargs.get('signs', -1)
            if signs not in [+1, -1]:
                raise ValueError('invalid signs')
            proc = AskProcessor(
                util.graph_to_generic_matrix(L, 'antisymmetric' if signs == -1 else 'symmetric')
                )
        else:
            proc = AskProcessor(L, mode=mode)
    elif objects == 'cico':
        proc = CicoProcessor(L, **kwargs)
    elif objects == 'adj':
        if not util.is_graph(L) and util.is_matrix(L):
            try:
                L = Graph(L)
            except:
                raise ValueError('input is not a graph or an adjacency matrix of a graph')
        proc = CicoProcessor(L, **kwargs)
    elif objects == 'inc':
        try:
            n = int(L)
            mu = kwargs.get('mu', {})
            A = cico.incidence_matrix_from_multiplicities(n, mu)
        except:
            A = Matrix(L)
        
        proc = IncidenceProcessor(A)
    elif objects == 'orbits':
        # NOTE: we don't currently check if L really spans a matrix Lie algebra
        proc = AskProcessor(util.matlist_to_mat(util.basis_of_matrix_algebra(L, product='Lie')), mode=mode)
    elif objects == 'cc':
        if not L.is_Lie() and not L.is_nilpotent():
            logger.warn('not a nilpotent Lie algebra')
            # raise ValueError('need a nilpotent Lie algebra in order to enumerate conjugacy classes')
        proc = AskProcessor(util.matlist_to_mat(L._adjoint_representation()), mode=mode)
    else:
        raise ValueError('unknown objects [%s]' % objects)

    if optimise_basis:
        logger.info('Searching for a good basis...')
        proc.optimise()
        logger.info('Picked a basis.')

    if verbose:
        print proc

    try:
        if type == 'p-adic':
            return proc.padically_evaluate(shuffle=True)
        elif type == 'topological':
            return proc.topologically_evaluate(shuffle=True)
    finally:
        if verbose:
            for ((m,_),level) in zip(loglevels,oldlevels):
                m.setLevel(level)

def do(type, L, objects='subalgebras', filename=None, save_memory=None, symbolic=False, **kwargs):
    if save_memory is None:
        save_memory = bool(type == 'p-adic')

    D = { 'optimise_basis': True,
          'strategy': Strategy.NORMAL if type == 'p-adic' else Strategy.PREEMPTIVE,
          'profile': Profile.SAVE_MEMORY if save_memory else Profile.NORMAL,
          'verbose': True,
          }

    if symbolic:
        common.symbolic = True
        D.update({ 'debug': True,
                   'addmany_dispatcher': 'symbolic',
                   'optlevel': 0.2 })
    else:
        common.symbolic = False

    D.update(kwargs)
    Z = zeta_function(type, L, objects, **D)
    if filename is True:
        if not isinstance(L, basestring):
            raise ValueError
        filename = objects + '-' + L + '.' + {'p-adic': 'pad', 'topological': 'top'}[type]
    if filename:
        with open(filename, 'w') as f: f.write(str(Z))
    return Z

topological_zeta_function = partial(do, 'topological', strategy=Strategy.NORMAL, verbose=False)
local_zeta_function = partial(do, 'p-adic', strategy=Strategy.NORMAL, verbose=False)

top = partial(do, 'topological')
pad = partial(do, 'p-adic')

def check(name, objects='subalgebras', type='p-adic', **kwargs):
    L = lookup(name)
    W = lookup(name, objects, type)
    if W is None:
        raise RuntimeError('zeta function not contained in database')

    Z = do(type, L, objects, **kwargs)
   
    if Z != W:
        print 'Computed: ', Z
        print 'Database: ', W
        raise RuntimeError('computed zeta function of %s differs from entry in the database' % name)

    print
    print 'Algebra #%d' % lookup(name,'id')
    print 'Names: %s' % ', '.join(lookup(name,'names'))
    print 'Objects:', objects
    print 'Type:', type
    print 'Zeta:', Z
    print 'Confirmed.'
    return True

def checkall(objects='reps', type='p-adic', **kwargs):
    ids = []

    for i, _ in lookup():
        if lookup(i, objects, type) is not None:
            check(i, objects, type, **kwargs)
            ids.append(i)

    print
    print 'Objects:', objects
    print 'Type:', type
    print 'Confirmed zeta functions for the following algebras:'

    for i in ids:
        print '#%d:\t%s' % (i, ', '.join(lookup(i, 'names')))
    print 'Total number:', len(ids)
    
if not common.normaliz:
    logger.warn('Normaliz not found. Triangulation will be slow.')
if not common.libcrunch:
    logger.warn('The C extension could not be loaded. Computations of topological zeta functions will use the slower Python implementation.')
if not common.count:
    logger.warn('LattE/count not found. Computations of p-adic zeta functions are unavailable.')
    
if __SERIES_BUG:
    logger.critical(
            """This version of Sage may compute incorrect symbolic power series
expansions. Computations of p-adic zeta functions are therefore
unavailable. Try using a different version of Sage such as 7.4.""")

    
def banner():
    return """
ZZZZZZZZZZZZZZZZZZZ                           tttt                           
Z:::::::::::::::::Z                        ttt:::t                           
Z:::::::::::::::::Z                        t:::::t                           
Z:::ZZZZZZZZ:::::Z                         t:::::t                           
ZZZZZ     Z:::::Z     eeeeeeeeeeee   ttttttt:::::ttttttt     aaaaaaaaaaaaa   
        Z:::::Z     ee::::::::::::ee t:::::::::::::::::t     a::::::::::::a  
       Z:::::Z     e::::::eeeee:::::et:::::::::::::::::t     aaaaaaaaa:::::a 
      Z:::::Z     e::::::e     e:::::tttttt:::::::tttttt              a::::a 
     Z:::::Z      e:::::::eeeee::::::e     t:::::t             aaaaaaa:::::a 
    Z:::::Z       e:::::::::::::::::e      t:::::t           aa::::::::::::a 
   Z:::::Z        e::::::eeeeeeeeeee       t:::::t          a::::aaaa::::::a 
ZZZ:::::Z     ZZZZe:::::::e                t:::::t    ttttta::::a    a:::::a 
Z::::::ZZZZZZZZ:::e::::::::e               t::::::tttt:::::a::::a    a:::::a 
Z:::::::::::::::::Ze::::::::eeeeeeee       tt::::::::::::::a:::::aaaa::::::a 
Z:::::::::::::::::Z ee:::::::::::::e         tt:::::::::::tta::::::::::aa:::a
ZZZZZZZZZZZZZZZZZZZ   eeeeeeeeeeeeee           ttttttttttt   aaaaaaaaaa  aaaa

%s
%s
                             by   
                                 Tobias Rossmann
""" % ('{:>77}'.format('VERSION ' + __version__),
       '{:>77}'.format('Released: ' + __date__))

print banner()

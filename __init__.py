#
# Zeta.
#
# Copyright 2014, 2015 Tobias Rossmann.
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

__version__ = '0.2'
__date__ = 'Mar 2015'

import common
import examples

from subobjects import SubobjectZetaProcessor
from reps import RepresentationProcessor

from algebra import Algebra
from abstract import ReductionError
from toric import ToricDatum
from util import create_logger

import surf
import abstract
import subobjects
import reps

from laurent import LaurentPolynomial

from subobjects import Strategy

from sage.all import Integer, Infinity, var

common.VERSION = __version__

logger = create_logger(__name__)

from reps import IgusaProcessor

class Profile:
    SAVE_MEMORY = 1
    NORMAL = 2
    SPEED = 3

def lookup(entry=None, what=None):
    if entry is None:
        return [(i, examples.names[i][:]) for i, _ in enumerate(examples.algebras)]
    i = examples.id.get(entry, entry)
    if what is None:
        try:
            return examples.algebras[i]
        except TypeError:
            raise KeyError('Invalid name of algebra')
        except IndexError:
            raise IndexError('Invalid index of algebra')
    if what == 'id':
        return i
    if what == 'names':
        return examples.names[i]
    return examples.topzetas[i].get(what, None)

def topological_zeta_function(L, objects, optimise_basis=False,
                              ncpus=None, strategy=None, profile=None, verbose=False):
    # Multiprocessing.
    if ncpus is None:
        ncpus = Infinity
    from multiprocessing import cpu_count
    common.ncpus = min(ncpus, cpu_count())

    # Reduction strategies.
    if strategy is None:
        strategy = Strategy.NORMAL

    # Memory profiles.
    if profile is None:
        profile = Profile.NORMAL
    if profile not in [Profile.SAVE_MEMORY, Profile.NORMAL, Profile.SPEED]:
        raise ValueError('Invalid profile')
    if profile == Profile.SAVE_MEMORY:
        common.disklist = True
        common.plumber = True
    elif profile == Profile.NORMAL:
        common.disklist = False
        common.plumber = True
    elif profile == Profile.SPEED:
        common.disklist = False
        common.plumber = False

    if verbose:
        from logging import INFO, DEBUG
        loglevels = [(logger, INFO), (surf.logger, INFO), (torus.logger, INFO), (abstract.logger, INFO), (reps.logger, DEBUG), (subobjects.logger, INFO)]
        oldlevels = []

        for m,level in loglevels:
            old = m.getEffectiveLevel()
            oldlevels.append(old)
            m.setLevel(min(old,level))

    # Try to detect polynomials and lists of polynomials.
    polynomials = None
    try:
        _ = L.exponents()
    except:
        try:
            if not isinstance(L, basestring):
                polynomials = list(L)
        except:
            pass
    else:
        polynomials = [L]
    
    if (polynomials is None) and not isinstance(L, algebra.Algebra):
        L = lookup(L)

    if polynomials is not None:
        proc = IgusaProcessor(*polynomials)
    elif objects in ['subalgebras', 'ideals']:
        proc = SubobjectZetaProcessor(L, objects, strategy=strategy)
    elif objects == 'reps':
        proc = RepresentationProcessor(L)
    else:
        raise ValueError('unknown objects')

    if optimise_basis:
        logger.info('Searching for a good basis...')
        proc.optimise()
        logger.info('Picked a basis.')

    if verbose:
        print proc

    try:
        return proc.topologically_evaluate(shuffle=True)
    finally:
        if verbose:
            for ((m,_),level) in zip(loglevels,oldlevels):
                m.setLevel(level)

def top(L, objects='subalgebras', filename=None, 
        optimise_basis=True, save_memory=False, ncpus=None, verbose=True):
    Z = topological_zeta_function(L,
                                  objects=objects,
                                  optimise_basis=optimise_basis,
                                  strategy=Strategy.PREEMPTIVE,
                                  profile=Profile.SAVE_MEMORY if save_memory else Profile.NORMAL,
                                  ncpus=ncpus,
                                  verbose=verbose)

    if filename is True:
        if not isinstance(L, basestring):
            raise ValueError
        filename = objects + '-' + L

    if filename:
        with open(filename, 'w') as f: f.write(str(Z))
    return Z

if not common.normaliz:
    logger.warn('Normaliz not found. Triangulation will be slow.')
if not common.libcrunch:
    logger.warn('C extension could not be loaded. Using slower Python implementation.')

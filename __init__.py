#
# Zeta.
#
# Copyright 2014 Tobias Rossmann.
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

__version__ = '0.1'
__date__ = 'Sep 2014'

import common
import examples

from algebra import Algebra
from reduction import ReductionError, Reductor
from toric import ToricDatum
from util import create_logger

import surf
import topological 

from sage.all import Integer, Infinity, var

common.VERSION = __version__

logger = create_logger(__name__)

from reduction import Strategy
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

def topological_zeta_function(L, objects='subalgebras', optimise_basis=False,
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
        loglevels = [(logger, INFO), (reduction.logger, INFO), (topological.logger, INFO), (surf.logger, INFO), (torus.logger, INFO)]
        oldlevels = []

        for m,level in loglevels:
            old = m.getEffectiveLevel()
            oldlevels.append(old)
            m.setLevel(min(old,level))

    # Construct toric datum.
    if not isinstance(L, algebra.Algebra) and not isinstance(L, ToricDatum):
        L = lookup(L)
    if isinstance(L,algebra. Algebra) and optimise_basis:
        logger.info('Searching for a good basis...')
        A = L.find_good_basis(objects)
        L = L.change_basis(A)
        logger.info('Picked a basis.')
    T = L if isinstance(L, ToricDatum) else L.toric_datum(objects)

    if verbose:
        print T

    try:
        return topological.evaluate(T, Reductor(strategy))
    #except reduction.ReductionError as e:
    #   logger.info('Failed to compute this topological zeta function: %s' % e)
    #   return None
    finally:
        if verbose:
            for ((m,_),level) in zip(loglevels,oldlevels):
                m.setLevel(level)

if not common.normaliz:
    logger.warn('Normaliz not found. Triangulation will be slow.')
if not common.libcrunch:
    logger.warn('C extension could not be loaded. Using slower Python implementation.')

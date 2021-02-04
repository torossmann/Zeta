from sage.all import *

from abc import ABCMeta, abstractmethod
from tmplist import TemporaryList

from util import TemporaryDirectory, readable_filesize

import surf
import common
import random

from contextlib import closing
from util import create_logger
logger = create_logger(__name__)

class ReductionError(Exception):
    pass

class ZetaDatum:
    __metaclass__ = ABCMeta

    @abstractmethod
    def is_empty(self):
        pass

    @abstractmethod
    def simplify(self):
        pass

    @abstractmethod
    def is_balanced(self):
        pass

    @abstractmethod
    def balance(self):
        return
        yield

    def is_ordered(self):
       return True

    def order(self):
       raise NotImplementedError

    @abstractmethod
    def is_regular(self):
        pass

    @abstractmethod
    def reduce(self, preemptive=False):
        pass

class GeneralZetaProcessor:
    __metaclass__ = ABCMeta

    @abstractmethod
    def root(self):
        pass

    def process(self, regular):
        with TemporaryList() as unprocessed:
            r = self.root()
            if r is not None:
                unprocessed.append(r)

            good = 0
            while unprocessed:
                datum = unprocessed.pop()
                logger.info('POP [#unprocessed = %2d, #regular = %d]' % (len(unprocessed)+1,len(regular)))

                datum = datum.simplify()

                if datum.is_empty():
                    continue

                if datum.is_regular():
                    good += 1
                    regular.append(datum)
                    continue

                # NOTE:
                # One could argue that there's really only ONE operation which
                # might act as balancing, ordering, reduction etc.
                #

                def do(things, name):
                    cnt = 0
                    for B in things:
                        if B.is_empty():
                            continue
                        unprocessed.append(B)
                        cnt += 1
                    logger.info('%s performed. Pushed %d new cases.' % (name, cnt))
                    
                try:
                    chops = list(datum.reduce(preemptive=True))
                except ReductionError:
                    pass
                else:
                    do(chops, 'Preemptive reduction')
                    continue

                if not datum.is_balanced():
                    logger.info('Balancing...')
                    do(datum.balance(), 'Balancing')
                    continue

                if not datum.is_ordered():
                    logger.info('Ordering...')
                    do(datum.order(), 'Ordering')
                    continue

                try:
                    chops = datum.reduce(preemptive=False)
                except ReductionError, e:
                    logger.debug("Don't know how to reduce this.")
                    raise e
                else:
                    do(chops, 'Reduction')
                    continue

        return regular

    def optimise(self):
        pass

class TopologicalZetaProcessor(GeneralZetaProcessor):
    __metaclass__ = ABCMeta

    @abstractmethod
    def topologically_evaluate_regular(self, datum):
        pass

    def topologically_evaluate(self, shuffle=False):
        with TemporaryList() as regular:
            #
            # Main loop.
            #
            logger.info('Beginning main loop.')
            self.process(regular)
            logger.info('Main loop finished successfully.')
            logger.info('Total number of regular data: %d' % len(regular))

            #
            # Evaluate.
            #
            with TemporaryDirectory() as evaldir:
                surfsum_names = [os.path.join(evaldir, 'surfsum%d' % k) for k in xrange(common.ncpus)]

                indices = range(len(regular))
                if shuffle:
                    random.shuffle(indices)

                def fun(k):
                    with closing(surf.SURFSum(surfsum_names[k])) as Q:
                        for i in xrange(k, len(regular), common.ncpus):
                            for S in self.topologically_evaluate_regular(regular[indices[i]]):
                                Q.add(S)
                    logger.info('Evaluator #%d finished.' % k)

                ET = sage.parallel.decorate.parallel(p_iter='reference' if common.debug else 'fork', ncpus=common.ncpus)(fun)
                logger.info('Launching %d evaluators.' % common.ncpus)
                for (arg, ret) in ET(range(common.ncpus)):
                    if ret == 'NO DATA':
                        raise RuntimeError('A parallel process died.')
                logger.info('All evaluators finished.')

                #
                # Crunch.
                #
                surfsums = []
                try:
                    surfsums = [surf.SURFSum(name) for name in surfsum_names]
                    return surf.multicrunch(surfsums)
                finally:
                    for Q in surfsums:
                        Q.close()

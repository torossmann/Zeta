from sage.all import *

from abc import ABCMeta, abstractmethod
from contextlib import closing
import random
import itertools

from .tmplist import TemporaryList, DiskList
from .util import TemporaryDirectory, readable_filesize
from . import addmany
from . import surf
from . import common
from .cycrat import CyclotomicRationalFunction

from .util import create_logger
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
                except ReductionError as e:
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
                surfsum_names = [os.path.join(evaldir, 'surfsum%d' % k) for k in range(common.ncpus)]

                indices = list(range(len(regular)))
                if shuffle:
                    random.shuffle(indices)

                def fun(k):
                    with closing(surf.SURFSum(surfsum_names[k])) as Q:
                        for i in range(k, len(regular), common.ncpus):
                            for S in self.topologically_evaluate_regular(regular[indices[i]]):
                                Q.add(S)
                    logger.info('Evaluator #%d finished.' % k)


                logger.info('Launching %d evaluators.' % common.ncpus)
                if not common.debug:
                    ET = sage.parallel.decorate.parallel(p_iter='fork', ncpus=common.ncpus)(fun)
                    for (arg, ret) in ET(list(range(common.ncpus))):
                        if ret == 'NO DATA':
                            raise RuntimeError('A parallel process died.')
                else:
                    logger.info('Serial execution enabled.')
                    for k in range(common.ncpus):
                        fun(k)
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

class LocalZetaProcessor(GeneralZetaProcessor):
    __metaclass__ = ABCMeta

    @abstractmethod
    def padically_evaluate_regular(self, datum):
        pass

    #def purge_denominator(self, denom):
    #    return denom

    # def degree_bound_in_t(self):
    #     """Returns an upper bound in 't' for the degree of a generic local zeta function.
    #     """
    #     return +Infinity

    # def degree_bound_in_q(self):
    #     """Returns an upper bound in 'q' for the degree of a generic uniform local zeta function.
    #     """
    #     return +Infinity

    def padically_evaluate(self, shuffle=False):
        with TemporaryList() as regular:
            logger.info('Beginning main loop.')
            self.process(regular)
            logger.info('Main loop finished successfully.')
            logger.info('Total number of regular data: %d' % len(regular))

            with TemporaryDirectory() as tmpdir:
                eval_filenames = [os.path.join(tmpdir, 'eval%d' % k)
                                  for k in range(common.ncpus)]

                def evaluate(k):
                    def fun(i):
                        try:
                            Q = DiskList(eval_filenames[k])
                            for a in self.padically_evaluate_regular(regular[i]):
                                Q.append(a)
                        except Exception as e:  # For debugging, change this to 'except RuntimeError as E'.
                            return e
                        else:
                            return True

                    if common.plumber and not common.debug:
                        fun = sage.parallel.decorate.fork(fun)

                    for i in range(k, len(regular), common.ncpus):
                        e = fun(i)
                        if e is not True:
                            raise e  # This will result in 'NO DATA' being returned below.
                    logger.info('Evaluator #%d finished.' % k)

                logger.info('Launching %d evaluators.' % common.ncpus)

                if not common.debug:
                    ET = sage.parallel.decorate.parallel(p_iter='fork', ncpus=common.ncpus)(evaluate)
                    for (arg, ret) in ET(list(range(common.ncpus))):
                        if ret == 'NO DATA':
                            raise RuntimeError('A parallel process died.')
                else:
                    logger.info('Serial execution enabled.')
                    for k in range(common.ncpus):
                        evaluate(k)
                logger.info('All evaluators finished.')

                if common.addmany_optimise:
                    eval_filenames = addmany.optimise(eval_filenames)

                logger.info('Total number of rational functions: %d' % sum(len(DiskList(f)) for f in eval_filenames))

                if common.addmany_dispatcher != 'symbolic':
                    denom = CyclotomicRationalFunction.common_denominator(itertools.chain.from_iterable(DiskList(f) for f in eval_filenames))
                    logger.info('Degree of denominator in (t,q): (%d,%d)'  % (-denom.degree(0), -denom.degree(1)))
                else:
                    denom = None

                # if common.addmany_dispatcher.find('interpol') != -1:
                #     purged_denom = self.purge_denominator(denom)
                #     logger.info('Degree of purged denominator in (t,q): (%d,%d)' % (-purged_denom.degree(0), -purged_denom.degree(1)))

                #     bound_t, bound_q = -Infinity, -Infinity
                #     for cr in itertools.chain.from_iterable(DiskList(f) for f in eval_filenames):
                #         bound_t = max(bound_t, cr.degree(0))
                #         bound_q = max(bound_q, cr.degree(1))
                #     logger.debug('bound_t = %d, bound_q = %d' % (bound_t,bound_q))
                # else:
                #     purged_denom = None
                #     bound_t = None
                #     bound_q = None

                ncpus = common.ncpus
                if common._alt_ncpus is not None:
                    common.ncpus = common._alt_ncpus

                try:
                    res = addmany.addmany(eval_filenames, denom)
                finally:
                    common.ncpus = ncpus

                with open(os.path.join(tmpdir, 'unfactored'), 'w') as f:
                    f.write(str(res))  # just in case factoring runs out of memory

                # Final recovery.
                logger.info('Factoring final result.')

                if res.parent() == SR:
                    res = res.factor() if res else res
                elif res:
                    fac = res.factor()
                    res = SR(fac.unit()) * SR.prod(SR(a)**i for a,i in fac)
                logger.info('All done.')
                return res

"""
Basic functionality for 'additively free ZZ-algebras', i.e. non-associative
ring structures on ZZ^n.
"""

from sage.all import *
from convex import PositiveOrthant
from toric import ToricDatum
from util import normalise_poly, monomial_log, cached_simple_method

import common
import multiprocessing

import itertools

class Algebra:
    """Additively free non-associative ZZ-algebras with optional operators.
    """

    def __init__(self, table=None, rank=None, operators=None,
                 matrix=None, bilinear=False, simple_basis=False,
                 descr=None, matrix_basis=None, product=None):

        """Construct an additively free ZZ-algebra (possibly with operators).
        """

        self.descr = descr
        self.operators = [] if (operators is None) else [Matrix(QQ,x) for x in operators]

        if not(matrix is None):
            A = Matrix(QQ,matrix)
            if not(bilinear or simple_basis):
                raise TypeError('You need to set either bilinear or simple_basis')

            if simple_basis:
                self.rank = A.ncols()
                e = MatrixSpace(QQ, self.rank).identity_matrix().rows()
                def f(i,j):
                    if abs(A[i,j]) > self.rank:
                        raise TypeError('Matrix entries out of range')
                    if   A[i,j] == 0: return (Integer(0) * e[0])
                    elif A[i,j] > 0:  return (e[A[i,j]-1])
                    elif A[i,j] < 0:  return (-e[-A[i,j]-1])
                self.table = [ [ f(i,j) for j in xrange(self.rank) ] for i in xrange(self.rank) ]
            elif bilinear:
                n = A.ncols()
                self.rank = n + Integer(1)
                w = vector(QQ, n * [Integer(0)] + [Integer(1)])
                self.table = [ [ A[i,j] * w for j in xrange(n) ] + [ 0 * w ] for i in xrange(n) ] + [ [ 0 * w for j in xrange(n+1) ] ]
            return
                
        # If the rank is set, always initialise an empty table.
        if not(rank is None):
            self.rank = rank
            self.table = [ [ vector(QQ, self.rank) for j in xrange(self.rank) ] for i in xrange(self.rank) ]

        if isinstance(table, dict):
            if rank is None:
                raise TypeError('You need to specify the rank') 
            for pos, v in table.iteritems():
                self.table[pos[0]][pos[1]] = vector(QQ, v)
            return

        if isinstance(table, list):
            self.rank = len(table)
            self.table = [ [ vector(QQ, v) for v in row ] for row in table ]
            return
        
        # 'basis' is a list of QQ-linearly independent matrixy things
        # spanning a Lie or associative algebra.
        if not(matrix_basis is None):
            if product is None:
                raise TypeError('need to specify Lie or associative product')
            if product == 'Lie':
                mult = lambda x, y: x*y - y*x
            elif product == 'associative':
                mult = lambda x, y: x*y
            else:
                raise TypeError('unknown type of product')

            self.rank = len(matrix_basis)
            matrix_basis = [Matrix(QQ, b) for b in matrix_basis]
            A = Matrix(QQ, [b.list() for b in matrix_basis])

            if A.rank() != len(matrix_basis):
                raise TypeError('matrices specified are linearly dependent')

            self.table = [ [ A.solve_left(vector(mult(b,c).list())) for c in matrix_basis] for b in matrix_basis ]
            return

        if rank is None:
            raise ValueError('need to specify the rank')

    def multiply(self, v, w, ring=QQ):
        return vector(ring, 
                      [ sum(v[i] * w[j] * self.table[i][j][k] for i in xrange(self.rank) for j in xrange(self.rank)) for k in xrange(self.rank) ]
                      )

    def ideal(self, vecs, ring=QQ):
        V = ring**self.rank
        B = list(identity_matrix(QQ,self.rank))
    
        U = V.subspace(vecs)
        while True:
            li = list(U.basis())
            xi = []
            for u,e in itertools.product(li,B):
                xi.append(self.multiply(u,e,ring=ring))
                xi.append(self.multiply(e,u,ring=ring))
            W = V.subspace(li+xi)
            if U == W:
                return U
            else:
                U = W

    @cached_simple_method
    def derived_series(self, ring=QQ):
        V = ring**self.rank
        dseries = [V]
        while True:
            W = self.ideal([self.multiply(v,w,ring=ring) for v in V.basis() for w in V.basis()])
            if V == W:
                return dseries
            else:
                V = W
                dseries.append(V)

    @cached_simple_method
    def derived_length(self):
        dseries = self.derived_series()
        return Infinity if dseries[-1].dimension() > 0 else len(dseries)-1

    @cached_simple_method
    def is_soluble(self):
        return self.derived_length() < Infinity

    @cached_simple_method
    def lower_central_series(self, ring=QQ):
        V = ring**self.rank
        B = list(V.basis())
        lcseries = [V]
        while True:
            li = []
            for v,e in itertools.product(V.basis(), B):
                li.append(self.multiply(v,e))
                li.append(self.multiply(e,v))
            W = self.ideal(li)
            if V == W:
                return lcseries
            else:
                V = W
                lcseries.append(V)

    @cached_simple_method
    def nilpotency_class(self):
        lcseries = self.lower_central_series()
        return Infinity if lcseries[-1].dimension() > 0 else len(lcseries)-1

    @cached_simple_method
    def is_nilpotent(self):
        return self.nilpotency_class() < Infinity

    @cached_simple_method
    def is_commutative(self):
        for u,v in itertools.product((QQ**self.rank).basis_matrix(),repeat=2):
            if self.multiply(u,v) != self.multiply(v,u):
                return False
        return True

    @cached_simple_method
    def is_anticommutative(self):
        for u,v in itertools.product((QQ**self.rank).basis_matrix(),repeat=2):
            if self.multiply(u,v) != -self.multiply(v,u):
                return False
        return True

    @cached_simple_method
    def is_associative(self):
        for u,v,w in itertools.product((QQ**self.rank).basis_matrix(),repeat=3):
            if self.multiply(self.multiply(u,v),w) != self.multiply(u,self.multiply(v,w)):
                return False
        return True

    @cached_simple_method
    def is_Lie(self):
        if not self.is_anticommutative():
            return False
        for u,v,w in itertools.product((QQ**self.rank).basis_matrix(),repeat=3):
            if self.multiply(self.multiply(u,v),w) != self.multiply(self.multiply(u,w),v) + self.multiply(u,self.multiply(v,w)):
                return False
        return True

    # Use rows of a matrix as the new basis.
    def change_basis(self, A):
        A = matrix(QQ, A)
        if not A.is_invertible():
            raise TypeError('The argument must be an invertible matrix over QQ.') 
        return Algebra( table = [[ self.multiply( A[i], A[j] ) * A.inverse() for j in xrange(self.rank) ] for i in xrange(self.rank)],
                        operators = [ A**(-1) * op * A for op in self.operators ]  )

    @cached_simple_method
    def _Lie_centre(self):
        # Construc the QQ-space of all z with a*z == z*a == 0 for all a.
        Z = QQ**self.rank
        for i in xrange(self.rank):
            Z = Z.intersection(
                matrix(QQ, [self.table[i][j] for j in xrange(self.rank)]).left_kernel()       
            )
            if self.is_anticommutative() or self.is_commutative():
                continue
            Z = Z.intersection(
                matrix(QQ, [self.table[j][i] for j in xrange(self.rank)]).left_kernel()
            )
        return Z

    @cached_simple_method
    def _adjusted_basis(self):
        # Construct a basis of 'self' as in (Stasinski & Voll 2014, Section 2.2.2);
        # we ignore finitely many primes.
        if not (self.is_Lie() and self.is_nilpotent() and self.rank > 0):
            raise NotImplementedError()

        Z = self._Lie_centre()
        D = self.derived_series()[1]

        M = Z.intersection(D)
        A = Z.intersection(M.complement())
        B = D.intersection(M.complement())
        C = (B+M+A).complement()
        li = list(itertools.chain(C.basis(), B.basis(), M.basis(), A.basis()))
        return matrix(QQ, [v.denominator()*v for v in li]), (dim(C), dim(B), dim(M), dim(A))

    @cached_simple_method
    def _commutator_matrices(self):
        A, dims = self._adjusted_basis()
        d = dims[1] + dims[2] # = dim of commutator ideal
        r = dims[0] + dims[1] # = codim of centre
        ring = PolynomialRing(QQ, 'y', d)
        y = vector(ring, ring.gens())

        T = self.change_basis(A)

        a = dims[0] ; b = a + d # [a,b) == indices of basis vectors of the commutator ideal

        R = matrix(ring, [
            [ y * vector(ring, [T.table[i][j][k] for k in xrange(a,b)])
              for j in xrange(r) ]
            for i in xrange(r) ]
                  )
        # get last dims[1] columns
        S = (R.transpose()[r-dims[1]:r]).transpose()
        return R, S

    def toric_datum(self, objects='subalgebras', name='x'):
        """Construct a toric datum associated with the enumeration of subobjects.

        We can enumerate subalgebras as well as left/right/2-sided ideals.
        """

        if not isinstance(objects, str):
            raise TypeError('String expected')
        if not objects in ['subalgebras', 'ideals', 'left ideals', 'right ideals']:
            raise TypeError('Unknown objects.')

        R = PolynomialRing(QQ, self.rank * (self.rank + 1) // 2, name)

        # Upper triangular matrices.
        cnt = 0
        M = matrix(R, self.rank, self.rank)
        for i in xrange(self.rank):
            for j in xrange(i, self.rank):
                M[i,j] = R.gen(cnt)
                cnt = cnt + 1

        D = prod(M.diagonal()) # D = det(M)

        zoo = prod(M[i,i]**(i+1) for i in xrange(self.rank))
        integrand = ( monomial_log(D), monomial_log(zoo) - vector(QQ,R.ngens() * [1]) )

        Madj = M.adjoint()

        E = identity_matrix(R, self.rank)
        li = []
        def insert_components(w):
            for rhs in w:
                if rhs.is_zero():
                    continue
                cand = normalise_poly(rhs)
                if not cand in li:
                    li.append(cand)

        for i in xrange(self.rank):
            for j in xrange(self.rank):
                if objects == 'subalgebras':
                    insert_components(self.multiply(M[i], M[j], R) * Madj)
                if (objects == 'right ideals') or (objects == 'ideals'):
                    insert_components(self.multiply(M[i], E[j], R) * Madj)
                if (objects == 'left ideals') or (objects == 'ideals'):
                    insert_components(self.multiply(E[j], M[i], R) * Madj)

        for op in self.operators:
            for row in M * matrix(R, op) * Madj:
                insert_components(row)

        if len(li) > 0:
            li = ideal(li).interreduced_basis()
        cc_raw = [(D,f) for f in li]

        # Perform some trivial simplifications
        cc = []
        for c in cc_raw:
            lhs, rhs = c
            if rhs.is_zero():
                continue
            g = gcd(lhs, rhs)
            rhs = rhs//g
            lhs = lhs//g
            if lhs.is_constant():
                continue
            mon, coeff = rhs.monomials(), rhs.coefficients()
            # Discard monomials in 'rhs' that are divisible by 'lhs'
            idx = [k for k in xrange(len(mon)) if not lhs.divides(mon[k])]
            rhs = sum(coeff[k] * mon[k] for k in idx)

            if rhs.is_zero():
                continue
            cand = (normalise_poly(lhs), normalise_poly(rhs))
            if not cand in cc:
                cc.append(cand) 
        cc.sort()
        T = ToricDatum(ring=R, integrand=integrand, cc=cc,
                               initials=None,
                               polyhedron=PositiveOrthant(R.ngens())
                               )
        return T.simplify()

    def find_good_basis(self, objects='subalgebras', name='x'):
        """Find a basis yielding a 'good' toric datum.
        
        Presently we only look at permutations of the given basis.
        """

        def weight(g):
            A = g.matrix()
            L = self.change_basis(A)
            return L.toric_datum(objects=objects, name=name).weight()

        best_weight, best_permutation = Infinity, None
        for (arg,w) in (parallel(ncpus=common.ncpus)(weight))(list(SymmetricGroup(self.rank))):
            g = arg[0][0]
            if w == 'NO DATA':
                w = weight(g)
            if w < best_weight:
                best_weight, best_permutation = w, g
        return matrix(QQ, best_permutation.matrix())

    
    def __str__(self):
        if self.descr:
            S = self.descr + '\n'
        else:
            S = "Additively free ZZ-algebra of rank " + str(self.rank) + " with multiplication table\n"

        for row in self.table:
            S = S + '\t'
            for vec in row:
                S = S + str(vec) + ', '
            S = S[:-2] + '\n'

        if len(self.operators) > 0:
            S += 'Operators: ' + str(len(self.operators)) + '\n'
 
        return S[:-1]

    def __repr__(self):
        return '%s(**%s)' % (self.__class__, self.__dict__)

def tensor_with_duals(L):
    n = L.rank
    shift = n * [n]
    zero  = n * [0]

    def f(i,j):
        if i < n and j < n:
            return list(L.table[i][j]) + zero
        elif i < n and j >= n:
            return zero + list(L.table[i][j-n])
        elif i >= n and j < n:
            return zero + list(L.table[i-n][j])
        else:
            return zero + zero
    return Algebra(table=[[f(i,j) for j in xrange(2*n)] for i in xrange(2*n)])

def tensor_with_3duals(L):
    n = L.rank
    shift = n * [n]
    zero  = n * [0]

    def f(i,j):
        if i < n and j < n:
            return list(L.table[i][j]) + zero + zero 
        elif i < n and n <= j < 2*n:
            return zero + list(L.table[i][j-n]) + zero
        elif i < n and 2*n <= j:
            return zero + zero + list(L.table[i][j-2*n])
        elif n <= i < 2*n and j < n:
            return zero + list(L.table[i-n][j]) + zero
        elif n <= i < 2*n and n <= j < 2*n:
            return zero + zero + list(L.table[i-n][j-n])
        elif 2*n <= i and j < n:
            return zero + zero + list(L.table[i-2*n][j])
        else:
            return zero + zero + zero
    return Algebra(table=[[f(i,j) for j in xrange(3*n)] for i in xrange(3*n)])


from sage.all import *

import common

from abstract import ZetaDatum, ReductionError, TopologicalZetaProcessor, LocalZetaProcessor
from convex import conify_polyhedron, RationalSet, PositiveOrthant
from reps import padically_evaluate_monomial_integral
from util import create_logger, cached_simple_method

from itertools import izip

logger = create_logger(__name__)

def other_vertex(edge, u):
    # Return the vertex of edge apart from u if there is one or u if it is a loop.
    return edge[1] if u == edge[0] else edge[0]

def make_edge(u, v):
    return tuple(sorted([u,v]))

def belongs_to_dual(vector, cone):
    return all(vector * ray >= 0 for ray in cone.rays())

def sort_edges(edges):
    return [tuple(sorted(e)) for e in edges]

def dominating_cones(vectors):
    assert vectors
    for j,v in enumerate(vectors):
        # 1st cone: v[0] * x < v[1] * x, ..., v[n] * x
        # 2nd cone: v[1] * x < v[2] * x, ..., v[n] * n; v[1] <= v[0]
        # ...
        # In particular, in the i-th cone returned, vectors[i] dominates
        # all others.
        ieqs = []
        for i,w in enumerate(vectors):
            if i == j:
                continue
            ieqs.append( [0 if i < j else -1] + list(w-v))
        yield Polyhedron(eqns=[], ieqs=ieqs, base_ring=QQ)

class CicoDatum(ZetaDatum):
    def __init__(self, *args, **kwargs):
        if not args:
            raise ValueError('no arguments provided')
        elif len(args) > 2:
            raise ValueError('too many arguments provided')

        # The first argument can be one of three things.
        
        # (1) Another CicoDatum.
        try:
            cd = args[0]
            self.nvertices = cd.nvertices
            self.edges = sort_edges(cd.edges)
            self.weights = list(cd.weights)
            self.signs = list(cd.signs)
            self.polyhedron = cd.polyhedron
            self.cone = cd.cone
            return
        except AttributeError:
            pass
        
        # (2) A non-negative integer indicating the number of vertices.
        try:
            nvertices = int(args[0])
            edges = sort_edges(args[1]) if len(args) == 2 else []
        except TypeError:
            # (3) A Sage graph.
            # NOTE: existing edge labels of the graph are quietly ignored!
            G = args[0]
            try:
                V = G.vertices()
                E = G.edges()
            except AttributeError:
                raise ValueError('input should be a graph')
            nvertices = len(V)
            I = range(nvertices)
            edges = sort_edges([ (V.index(u), V.index(v)) for u,v,_ in E])


        if any(a not in range(nvertices) for a in flatten(edges)):
            raise ValueError('invalid edges [indices]')

        if any(len(e) not in [1,2] for e in edges):
            raise ValueError('invalid edges [counts]')

        edges = [(e[0], e[1]) if len(e) == 2 else (e[0],e[0]) for e in edges]
        
        signs = kwargs.get('signs', -1)
        if signs in [+1, -1]:
            signs = len(edges) * [signs]
            
        if any(s not in [+1, -1] for s in signs):
            raise ValueError('invalid signs')

        weights = kwargs.get('weights', len(edges) * [(ZZ**nvertices)(0)])
        if any(w not in (ZZ**nvertices) for w in weights):
            raise ValueError('invalid weights')

        if not(len(edges) == len(weights) == len(signs)):
            raise ValueError('mismatch between edges, weights, and signs')

        polyhedron = kwargs.get('polyhedron', PositiveOrthant(nvertices))
        cone = conify_polyhedron(polyhedron)

        # Confirm that the weight axiom of WSMs is satisfied.
        I = identity_matrix(ZZ, nvertices)
        if any(not belongs_to_dual(I[i] + weights[j], cone)
               for j,e in enumerate(edges)
               for i in set(e)):
            raise ValueError('the weights and the polyhedron are incompatible')
        
        self.nvertices = nvertices
        self.edges = edges
        self.weights = list(weights)
        self.signs = list(signs)
        self.polyhedron = polyhedron
        self.cone = cone

    def sage_graph(self):
        sage_edges = [ (e[0],e[1],{'weight': w, 'sign': s, 'index': i})
                       for (i,e),w,s in zip(enumerate(self.edges), self.weights, self.signs) ]
        return Graph([range(self.nvertices),sage_edges], loops=True, multiedges=True)
        
    def clone(self):
        return CicoDatum(self)
    
    def is_empty(self):
        return self.polyhedron.is_empty()

    @cached_simple_method
    def is_solitary(self):
        return all(u == v for u,v in self.edges)

    @cached_simple_method
    def has_multiple_edges(self):
        return self.sage_graph().has_multiple_edges()
        
    @cached_simple_method
    def is_balanced(self):
        return self.is_solitary() and (not self.has_multiple_edges())

    @cached_simple_method
    def is_regular(self):
        return self.is_balanced()

    def desocialise(self):
        if self.is_solitary():
            yield self
            return

        # Pick a social connected component C.
        G = self.sage_graph()
        C = next(C for C in G.connected_components() if len(C) > 1)
        component_edge_indices = [i for i,(u,v) in enumerate(self.edges) if u in C]

        # Populate `candidates' with all pairs (i,u), where i is the index of
        # an edge contained in C and u lies on this edge.
        candidates = []
        for i in component_edge_indices:
            u,v = self.edges[i]
            candidates.append((i,u))
            if u != v:
                candidates.append((i,v))

        # Find the adjusted weights to be balanced in order to obtained a
        # total preorder w.r.t. domination of incident pairs.
        I = identity_matrix(ZZ, self.nvertices)
        vectors = [self.weights[i] + I[u] for i,u in candidates]
        
        for (i,u),P in izip(candidates, dominating_cones(vectors)):
            e = self.edges[i]
            v = other_vertex(e, u)

            cd = self.clone()

            # Shrink the polyhedron.
            cd.polyhedron &= P
            if cd.polyhedron.is_empty():
                continue
           
            if u != v:
                # Case: h = uv is a dominant non-loop.
                
                for j in component_edge_indices:
                    # NOTE: This loop will do nothing if (u,v) is already a spike.
                    
                    h = self.edges[j]
                    # Consider all edges touching v, other than e.
                    if (h == e) or (v not in h): 
                        continue
                    
                    w = other_vertex(h, v)

                    # Picture:
                    #      e         f
                    # u ------- v ------- w
                    #
                    if v == w:
                        # Dominant non-loop vs loop.
                        cd.edges[j] = make_edge(u,u)
                        cd.weights[j] += 2 * (I[v] - I[u])
                        cd.signs[j] = +1 # It doesn't really matter, it's a loop.
                    else:
                        # Dominant non-loop vs non-loop.
                        cd.edges[j] = make_edge(u, w)
                        cd.weights[j] += I[v] - I[u]
                        cd.signs[j] = (-1) * cd.signs[i] * cd.signs[j]

                # Now (u,v) should be a spike.
                # Let's double check to make sure that there are no edges parallel to e
                # with different signs.
                # If they all have the same sign, we can just trim all parallel spikes at
                # once.

                all_parallels = [j for j,f in enumerate(cd.edges) if e == f]

                if any(cd.signs[i] != cd.signs[j] for j in all_parallels):
                    raise RuntimeError('Opposing parallel edges should have been removed')
                
                # Trim the spike.
                for j in all_parallels:
                    cd.edges[j] = make_edge(v, v)
                    cd.weights[j] += I[u] - I[v]
                    cd.signs[j] = +1 # Again, the sign doesn't actually matter.
                    
                yield cd
            else: # if u == v
                # Case: h = u^2 is a dominant loop.
                
                for j in component_edge_indices:
                    h = self.edges[j]
                    if u not in h or h == e:
                        continue
                    w = other_vertex(h, u)

                    cd.edges[j] = make_edge(w, w)
                    cd.weights[j] += I[u] - I[w]
                    cd.signs[j] = +1

                    # NOTE: In the paper, the operations above are justified
                    # in the case that u != w.
                    # Otherwise, the only thing that might be changing is the
                    # sign of h and this doesn't matter anyway.

                yield cd

    def deparallelise(self):
        # Remove some parallel edges if there are any.
        # We assume that there are no parallel non-loops with opposite signs.
        # These are taken care of in `balance'.
        
        G = self.sage_graph()
        E = G.multiple_edges()

        if not E:
            yield self
            return

        u,v,_ = E[0]
        indices = [C['index'] for a,b,C in E if (a,b) == (u,v)]

        assert len(indices) > 1
        assert (u == v) or all(self.signs[i] == self.signs[indices[0]] for i in indices[1:])
        
        vectors = [self.weights[i] for i in indices]
        
        for i,P in izip(indices, dominating_cones(vectors)):
            cd = self.clone()
            cd.polyhedron &= P
            other_indices = [j for j in range(len(cd.edges)) if j == i or j not in indices]
            cd.edges = [cd.edges[j] for j in other_indices]
            cd.weights = [cd.weights[j] for j in other_indices]
            cd.signs = [cd.signs[j] for j in other_indices]
            yield cd
            
    def _opposing_parallel_nonloop_edges(self):
        return next(
            ((i,j)
            for i,e in enumerate(self.edges)
            for j,f in enumerate(self.edges)
             if e == f and e[0] != e[1] and self.signs[i] != self.signs[j]),
            None)

    def balance(self):
        if self.is_balanced():
            yield self
            return

        # If there are any, first get rid of parallel non-loops with
        # opposite signs.
        res = self._opposing_parallel_nonloop_edges()
        if res is not None:
            I = identity_matrix(self.nvertices)
            i,j = res

            for k,ell,P in zip([i,j], [j,i], dominating_cones([self.weights[i], self.weights[j]])):
                # Now `k' dominates `ell'.

                cd = self.clone()
                cd.polyhedron &= P
                
                if cd.polyhedron.is_empty():
                    continue

                u,v = self.edges[k]
                
                assert (u,v) == self.edges[ell]
                
                cd.edges[ell] = make_edge(v,v)
                cd.weights[ell] += I[u] - I[v]
                yield cd
            return

        # Next, if our graph is social, do something about that.
        if not self.is_solitary():
            for z in self.desocialise():
                yield z
            return

        # Finally, deal with parallel edges that are loops or that
        # have the same sign.
        for z in self.deparallelise():
            yield z
        return
        
    def reduce(self, preemptive=False):
        raise ReductionError

    def simplify(self):
        return self
    
    def __repr__(self):
        s = 'CicoDatum\n'
        s += 'Number of vertices: %d\n' % self.nvertices
        s += 'Edges: %s\n' % self.edges
        s += 'Weights: %s\n' % self.weights
        s += 'Signs: %s\n' % self.signs
        s += 'Polyhedron:\n%s' % str(self.polyhedron.Hrepresentation())
        return s

class CicoProcessor(TopologicalZetaProcessor, LocalZetaProcessor):
    def __init__(self, *args, **kwargs):
        self._root = CicoDatum(*args, **kwargs)
        self.nvertices = self._root.nvertices

    def __repr__(self):
        return 'Cico processor:\nRoot:\n%s' % self._root
        
    @cached_simple_method
    def root(self):
        return self._root

    def topologically_evaluate_regular(self, datum):
        raise NotImplementedError
    
    def padically_evaluate_regular(self, datum):
        # Our integral is
        # |y|^(s-1) * prod_v ||x^(v + weight) : weight in wt(v); y||^(-1).
        if not datum.is_regular():
            raise ValueError('need a regular datum')
                                     
        n = self.nvertices
        RS = RationalSet([datum.polyhedron]) * RationalSet(PositiveOrthant(1))

        polytopes = [ Polyhedron(vertices=[vector(ZZ, n * [0] + [1])]) ]

        I = identity_matrix(ZZ, n)

        vertices = [ [vector(ZZ, n * [0] + [1]) ] for _ in range(n)] # y appears in each factor

        for i,(u,v) in enumerate(datum.edges):
            assert u == v and u in range(n)
            vertices[u].append(vector(ZZ, list(I[u] + datum.weights[i]) +  [0]))
            
        for v in vertices:
            polytopes.append(Polyhedron(vertices=v))

        for z in padically_evaluate_monomial_integral(RS, polytopes,
                                                      [(1,) + n * (0,), (n + 1) * (1,)]):
            yield z

    def padically_evaluate(self, shuffle=False):
        if self.root() is None:
            return SR(1)
        r = ((1 - SR('q')**(-1))**self.nvertices * LocalZetaProcessor.padically_evaluate(self, shuffle=shuffle)).factor()
        return r

class IncidenceDatum(ZetaDatum):
    def __init__(self, A):
        if any(entry not in [0,1] for row in A for entry in row):
            raise ValueError('not an incidence matrix')
        
        self.A = copy(A)
        self.d = A.nrows()
        self.e = A.ncols()

    def is_empty(self):
        return self.d == 0

    def simplify(self):
        return self

    def is_balanced(self):
        return True

    def balance(self):
        yield self
        return
    
    def is_regular(self):
        return True

    def reduce(self, preemptyive=False):
        raise ReductionError('not needed')

    def __repr__(self):
        return 'IncidenceDatum:\n' + repr(self.A)

class IncidenceProcessor(TopologicalZetaProcessor, LocalZetaProcessor):
    def __init__(self, A):
        self._root = IncidenceDatum(A)
        self.nvertices = A.nrows()
        self.nedges = A.ncols()
        self.A = copy(A)

    @cached_simple_method
    def root(self):
        return self._root
    
    def __repr__(self):
        return 'Incidence processor.\nRoot:\n' + repr(self._root)

    def topologically_evaluate_regular(self, datum):
        raise NotImplementedError
    
    def padically_evaluate_regular(self, datum):
        A = self.A
        n = self.nvertices
        m = self.nedges

        RS = RationalSet(PositiveOrthant(n + 1))

        polytopes = [Polyhedron(vertices=[vector(ZZ, n * [0] + [1])])]

        I = list(identity_matrix(ZZ, n + 1))
                 
        for j in range(m):
            vertices = [vector(ZZ, n * [0] + [1])]
            for i,a in enumerate(A.column(j)):
                if a == 1:
                    vertices.append(I[i])
            polytopes.append(Polyhedron(vertices=vertices))

        for z in padically_evaluate_monomial_integral(RS, polytopes,
                                                      [(1,) + m * (0,), (m + 1) * (1,)]):
            yield z

    def padically_evaluate(self, shuffle=False):
        t,q = var('t q')
        if self.nvertices == 0:
            return 1/(1-t)
        W = LocalZetaProcessor.padically_evaluate(self, shuffle=shuffle).factor()
        assert W
        r = ((1 - q**(-1))**self.nvertices * W(t=q**(self.nvertices-self.nedges)*t)).factor()
        return r

def incidence_matrix_from_multiplicities(n, mu):
    m = sum(mu.values())
    A = Matrix(n, m)
    j = 0
    for support,multiplicity in mu.items():
        if multiplicity < 0:
            raise ValueError('invalid multiplicity')
        if any(x not in range(n) for x in support):
            raise ValueError('invalid support')
        
        col = [1 if i in support else 0 for i in range(n)]
        for _ in range(multiplicity):
            A.set_column(j, col)
            j += 1
    return A
    

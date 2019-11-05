def isogeny_graph(p,ell):
    """
    Computes the ell-isogeny graph of supersingular elliptic curves in characteristic p.

    The inputs are a prime p, assumed to be congruent to 1 mod 12, ell a prime different from p.
    The function outputs a dictionary whose keys are j invariants, and the value of j is a dictionary of
    neighboring j-invariants j', the value of j' being the edges between j and j' (the output of find_neighbors(E(j),ell).
    The function first computes one supersingular j invariant using the CM method. We add j = j(E) and
    its neighbors to the graph dictionary, then add the neighbors of j to a temporary list, irregular_vertices.
    Then we grab a pair (j',phi) from irregular_vertices, add j' along with its neighbors to the graph. Now the graph is
    ell+1-regular at j', so we remove (j',phi) from irregular_vertices. Each neighbor j'' of j' is either
    already a key in the dictionary, meaning we have computed it and all of its neighbors, or we have visited it but not
    yet found all its neighbors, or we have never visited it. If this is the first visit to j'', we add it to
    irregular_vertices. The output is Gpell, which stores the j-invariants, curves (all in the same isogeny class),
    and isogenies used to represent edges, along with either a graph or directed graph SAGE object for G(p,ell).
    """

    F = GF(p^2)
    if not p.is_prime() and ell.is_prime():
        raise ValueError, 'inputs must be primes'
    elif p%12 == 7:
        E = EllipticCurve([F(1),F(0)])
        j = E.j_invariant()
        epsilon = 1
    elif p%12 == 5:
        E = EllipticCurve([F(0),F(1)])
        j = E.j_invariant()
        epsilon = 1
    elif p%12 == 11:
        E = EllipticCurve([F(0),F(1)])
        j = E.j_invariant()
        epsilon = 2
    else:
        q = 3
        while kronecker(-q,p) == 1 or q%4 == 1:
            q = next_prime(q)
        PK = hilbert_class_polynomial(-q)
        Fx = F['x']
        PK = Fx(PK)
        j = PK.roots()[0][0]
        E = EllipticCurve(j=j)
        epsilon = 0
    Gpell = {}
    irregular_vertices = []
    neighbors = find_neighbors(E,ell)
    Gpell[j] = {}
    Gpell[j]['curve'] = E
    Gpell[j]['neighbors'] = find_neighbors(E,ell)
    finished_vertices = 1
    graph_size = int(p/12) + epsilon
    for vertex in Gpell[j]['neighbors']:
        edge = Gpell[j]['neighbors'][vertex]
        irregular_vertices.append((vertex, edge))
    while finished_vertices < graph_size:
        edge = irregular_vertices.pop(0)
        j = edge[0]
        phi = edge[1][0]
        if j in Gpell:
            continue
        phiE = phi.codomain()
        Gpell[j] = {}
        Gpell[j]['curve'] = phiE
        Gpell[j]['neighbors'] = find_neighbors(phiE,ell)
        finished_vertices = finished_vertices + 1
        for vertex in Gpell[j]['neighbors']:
            if vertex in Gpell:
                continue
            edges = Gpell[j]['neighbors'][vertex]
            irregular_vertices.append((vertex, edges))
    graph_dict = {}
    for j in Gpell:
        neighbors = []
        for vertex in Gpell[j]['neighbors']:
            edges = Gpell[j]['neighbors'][vertex]
            for phi in edges:
                neighbors.append(vertex)
        graph_dict[j] = neighbors
    if p%12 == 1:
        return Gpell, Graph(graph_dict)
    else:
        return Gpell, DiGraph(graph_dict)


def find_neighbors(E,ell):
    """
    Computes the isosogenies whose kernels are the ell+1 nonzero cyclic subgroups of E[ell].

    The output is a dictionary, whose keys are the neighbor j-invariants and the value of j' is a
    list of isogenies between E and E(j').
    """

    F = E.base_field()
    if ell == 2:
        R.<x> = F['x']
        f = x^3 + F(E.a_invariants()[3])*x + F(E.a_invariants()[4])
        kernel_polys = [factor[0] for factor in f.factor()]
    else:
        factors = E.division_polynomial(ell).factor()
        factors = [div[0] for div in factors]
        kernel_polys = []
        while len(factors)>0:
            div = factors.pop(0)
            if div.degree() == (ell-1)/2:
                kernel_polys.append(div)
            else:
                L.<c> = F.extension(2)
                R.<x> = F['x']
                xP = -div[0]
                EL = E.change_ring(L)
                yP = find_y_coordinate(EL,L(xP))
                P = EL(L(xP),yP)
                Q = P
                kernel_poly = (x-xP)
                for k in range(2,ell):
                    Q = Q + P
                    xQ = F(Q[0])
                    if not (x-xQ).divides(kernel_poly):
                        kernel_poly = kernel_poly*(x-xQ)
                        if (x-xQ) in factors:
                            factors.remove(x-xQ)
                kernel_polys.append(kernel_poly)
    edges = {}
    for kernel_poly in kernel_polys:
        phi = EllipticCurveIsogeny(E,kernel_poly)
        phiE = phi.codomain()
        j = phiE.j_invariant()
	if j in edges:
            multiple_edges = edges[j]
            multiple_edges.append(phi)
	    edges[j] = multiple_edges
	else:
            edges[j] = [phi]
    return edges



def torsion_gens(E,ell):
    """
    Computes a basis of the ell-torsion of E, where ell is a prime number.

    The output is P, Q,  E', iota where E' over L is the base change of E to a field extension L over F such that
    E(L) contains E[ell]. The points P and Q generate E[ell]. iota is the embedding of F into L used for
    base changing E over F to E over L.
    """

    from sage.rings.finite_rings.hom_finite_field import FiniteFieldHomomorphism_generic
    import random
    p = E.base_field().characteristic()
    base_degree = E.base_field().degree()
    F = GF(p^(base_degree))
    coerce_base_field = FiniteFieldHomomorphism_generic(Hom(E.base_field(),F))
    E_over_F = coerce_curve(E,coerce_base_field)
    psi = E_over_F.division_polynomial(ell)
    factors = psi.factor()
    f = factors[0][0]
    d = f.degree()
    K = GF(p^(d*base_degree))
    L = GF(p^(2*d*base_degree))
    embed_F_to_K = FiniteFieldHomomorphism_generic(Hom(F,K))
    embed_K_to_L = FiniteFieldHomomorphism_generic(Hom(K,L))
    new_factors = coerce_poly(f, embed_F_to_K).factor()
    xP = -new_factors[0][0][0]
    E_over_L = coerce_curve(E_over_F, (embed_K_to_L)*(embed_F_to_K))
    xP = embed_K_to_L(xP)
    yP = find_y_coordinate(E_over_L, xP)
    P = E_over_L(xP,yP)
    Q = P
    while P.weil_pairing(Q,ell) == 1:
        f = random.choice(list(factors))[0]
        newK = GF(p^(base_degree*f.degree()))
        newL = GF(p^(2*base_degree*f.degree()))
        compositum_degree = lcm(L.degree(), newL.degree())
        compositum = GF(p^(compositum_degree))
        embed_F_to_newK = FiniteFieldHomomorphism_generic(Hom(F,newK))
        embed_newK_to_compositum = FiniteFieldHomomorphism_generic(Hom(newK,compositum))
        E_over_compositum = coerce_curve(E_over_F,(embed_newK_to_compositum)*(embed_F_to_newK))
        new_factors = coerce_poly(f, embed_F_to_newK).factor()
        xQ = -(random.choice(list(new_factors))[0][0])
        xQ = embed_newK_to_compositum(xQ)
        yQ = find_y_coordinate(E_over_compositum,xQ)
        Q = E_over_compositum(xQ,yQ)
        P = E_over_compositum(xP,yP)
    return P, Q, E_over_compositum, (embed_newK_to_compositum)*(embed_F_to_newK)*(coerce_base_field)

def coerce_poly(f, iota):
    R = iota.codomain()[x]
    g = R(0)
    for k in range(f.degree()+1):
        g = g + iota(f[k])*R(x^k)
    return g

def coerce_curve(E, iota):
    E = EllipticCurve([iota(a) for a in E.a_invariants()])
    return E




def trace_of_chain(chain):
    """
    Given a chain of isogenies in G(p,ell) representing an endomorphism phi, computes the trace of phi.

    First we find a list of primes q1,...,qk such that q1*...*qk > 2*(deg phi)^(1/2).
    Then for each prime qj, we compute the trace of phi mod qj with trace_mod_m.
    Then we recover the trace with generalCRT.
    """
    p = chain[0].domain().base_field().characteristic()
    ell = chain[0].degree()
    e = len(chain)
    N = 3
    moduli = [3]
    traces = []
    q = 3
    while N < 2*sqrt(float(ell^e)):
        q = next_prime(q);
        if q != p:
            N = N*q
            moduli.append(q)
    for M in moduli:
        traces.append(trace_mod_prime(M, chain))
    trace = general_CRT(traces, moduli)
    if trace > N/2:
        return trace - N
    else:
        return trace

def trace_mod_prime(M, chain):
    """
    Computes the trace mod M of alpha, where M is a prime not equal to 2,p.

    Let phi = phi_e-1 * ... * phi_0, where phi_k is chain[k]. We compute the trace of phi modulo M
    by computing generators P1,P2 of E[M]
    and checking whether phi^2(P_i) - [t]phi(P_i) + [degphi]P_i = 0 holds on E[m]. if so, return t.
    """

    E = chain[0].domain()
    if chain[len(chain)-1].codomain() != E:
        raise ValueError, 'Chain does not represent an endomorphism'
    degree = 1
    for phi in chain:
        degree = degree*phi.degree()
    R = test_point(E)
    phiR = evaluate_chain(chain,R)
    P, Q, newE, embedding = torsion_gens(E,M)
    new_chain = base_change_chain(chain, embedding)
    flag = (evaluate_chain(new_chain,coerce_point(R, newE, embedding)) == coerce_point(phiR, newE, embedding))
    phiP = evaluate_chain(new_chain, P)
    phiQ = evaluate_chain(new_chain, Q)
    phiphiP = evaluate_chain(new_chain, phiP)
    phiphiQ = evaluate_chain(new_chain, phiQ)
    degM = (degree)%M
    for k in range(M):
        if phiphiP - k*phiP + degM*P == newE(0):
            if phiphiQ - k*phiQ + degM*Q == newE(0):
                if flag:
                    return k
                else:
                    return -k

def general_CRT(values,moduli):
    """
    Given coprime moduli m_1,...,m_n and values a_1,... a_n, this returns x such that x mod m_k = a_k for each k.
    """
    x = values[0]
    M = moduli[0]
    for k in range(1, len(values)):
        x = crt(x, values[k], M, moduli[k])
        M = M*moduli[k]
    return x


def path_to_chain(path,Gpell):
    """
    Returns a chain of isogenies between the vertices in path in the graph Gpell.

    The domain of phi_k is the codomain of phi_{k-1}. The purpose of this is that if G(p,ell)
    is constructed from isogeny_graph( ... ), domains and codomains of edges
    don't agree always.
    """
    p = path[0].parent().characteristic()
    F = GF(p^2)
    R = F['x']
    chain = []
    for k in range(len(path)-1):
        E = Gpell[path[k]]['curve']
        phi = Gpell[path[k]]['neighbors'][path[k+1]][0]
        phiE = Gpell[path[k+1]]['curve']
        f = phi.kernel_polynomial()
        f = R(f)
        phi = EllipticCurveIsogeny(E,f,phiE)
        chain.append(phi)
    return chain



def dual_chain(chain):
    dualChain = []
    for phi in chain:
        dualChain.insert(0,phi.dual())
    return dualChain

def find_y_coordinate(E,xP):
    """
    Computes yP such that (xP,yP) is a point P of E, if such a yP exists.
    """

    R.<y> = (E.base_field())['y']
    a1,a2,a3,a4,a6 = E.a_invariants()
    G = y^2 +(a1*xP+a3)*y-xP^3-a2*xP^2-a4*xP-a6
    factor = G.factor()[0][0]
    if factor.degree()>1:
        raise ValueError, 'Point is not defined over ',E.base_field()
    else:
        return -factor[0]



def evaluate_chain(chain,P):
    """
    Evaluates the isogeny chain at a point P.
    """

    Q = P
    for phi in chain:
        Q = phi(Q)
    return Q

def base_change_chain(chain,iota):
    """
    This coerces a chain of isogenies using the field embedding iota.

    The input chain is a sequence of isogenies defined over a field F, and iota: F to L is a field embedding.
    The output basechange(chain,iota) returns the same chain of isogenies but now they can be evaluated at points
    defined over L. We use this to evaluate endomorphisms
    at points of E[m] which may not be defined over base field of E.
    """

    new_chain = []
    for k in range(len(chain)):
        domain = coerce_curve(chain[k].domain(),iota)
        codomain = coerce_curve(chain[k].codomain(),iota)
        kerPoly = coerce_poly(chain[k].kernel_polynomial(),iota)
        new_chain.append(EllipticCurveIsogeny(domain,kerPoly,codomain))
    return new_chain

def coerce_point(P,E,iota):
    """
    Coerces a point P onto E using iota.

    Here, iota is an embedding of a field F into an extension K. E is the base change to K of a curve E' over F,
    and P is a point on E'. The embedding iota is used to coerce the coordinates of P.
    """

    P = E(iota(P[0]),iota(P[1]))
    return P

def test_point(E):
    P = E.random_point()
    while 2*P == E(0):
        P = E.random_point()
    return P
def isogeny_graph(p,ell):
    """
    Computes the ell-isogeny graph of supersingular elliptic curves in characteristic p.

    The inputs are a prime p, assumed to be congruent to 1 mod 12, ell a prime different from p.
    The function outputs a dictionary whose keys are j invariants, and the value of j is a dictionary of
    neighboring j-invariants j', the value of j' being the edges between j and j' (the output of find_neighbors(E(j),ell).
    The function first computes one supersingular j invariant using the CM method. We add j = j(E) and
    its neighbors to the graph dictionary, then add the neighbors of j to a temporary list, irregular_vertices.
    Then we grab a pair (j',phi) from irregular_vertices, add j' along with its neighbors to the graph. Now the graph is
    ell+1-regular at j', so we remove (j',phi) from irregular_vertices. Each neighbor j'' of j' is either
    already a key in the dictionary, meaning we have computed it and all of its neighbors, or we have visited it but not
    yet found all its neighbors, or we have never visited it. If this is the first visit to j'', we add it to
    irregular_vertices. The output is Gpell, which stores the j-invariants, curves (all in the same isogeny class),
    and isogenies used to represent edges, along with either a graph or directed graph SAGE object for G(p,ell).
    """

    F = GF(p^2)
    if not p.is_prime() and ell.is_prime():
        raise ValueError, 'inputs must be primes'
    elif p%12 == 7:
        E = EllipticCurve([F(1),F(0)])
        j = E.j_invariant()
        epsilon = 1
    elif p%12 == 5:
        E = EllipticCurve([F(0),F(1)])
        j = E.j_invariant()
        epsilon = 1
    elif p%12 == 11:
        E = EllipticCurve([F(0),F(1)])
        j = E.j_invariant()
        epsilon = 2
    else:
        q = 3
        while kronecker(-q,p) == 1 or q%4 == 1:
            q = next_prime(q)
        PK = hilbert_class_polynomial(-q)
        Fx = F['x']
        PK = Fx(PK)
        j = PK.roots()[0][0]
        E = EllipticCurve(j=j)
        epsilon = 0
    Gpell = {}
    irregular_vertices = []
    neighbors = find_neighbors(E,ell)
    Gpell[j] = {}
    Gpell[j]['curve'] = E
    Gpell[j]['neighbors'] = find_neighbors(E,ell)
    finished_vertices = 1
    graph_size = int(p/12) + epsilon
    for vertex in Gpell[j]['neighbors']:
        edge = Gpell[j]['neighbors'][vertex]
        irregular_vertices.append((vertex, edge))
    while finished_vertices < graph_size:
        edge = irregular_vertices.pop(0)
        j = edge[0]
        phi = edge[1][0]
        if j in Gpell:
            continue
        phiE = phi.codomain()
        Gpell[j] = {}
        Gpell[j]['curve'] = phiE
        Gpell[j]['neighbors'] = find_neighbors(phiE,ell)
        finished_vertices = finished_vertices + 1
        for vertex in Gpell[j]['neighbors']:
            if vertex in Gpell:
                continue
            edges = Gpell[j]['neighbors'][vertex]
            irregular_vertices.append((vertex, edges))
    graph_dict = {}
    for j in Gpell:
        neighbors = []
        for vertex in Gpell[j]['neighbors']:
            edges = Gpell[j]['neighbors'][vertex]
            for phi in edges:
                neighbors.append(vertex)
        graph_dict[j] = neighbors
    if p%12 == 1:
        return Gpell, Graph(graph_dict)
    else:
        return Gpell, DiGraph(graph_dict)


def find_neighbors(E,ell):
    """
    Computes the isosogenies whose kernels are the ell+1 nonzero cyclic subgroups of E[ell].

    The output is a dictionary, whose keys are the neighbor j-invariants and the value of j' is a
    list of isogenies between E and E(j').
    """

    F = E.base_field()
    if ell == 2:
        R.<x> = F['x']
        f = x^3 + F(E.a_invariants()[3])*x + F(E.a_invariants()[4])
        kernel_polys = [factor[0] for factor in f.factor()]
    else:
        factors = E.division_polynomial(ell).factor()
        factors = [div[0] for div in factors]
        kernel_polys = []
        while len(factors)>0:
            div = factors.pop(0)
            if div.degree() == (ell-1)/2:
                kernel_polys.append(div)
            else:
                L.<c> = F.extension(2)
                R.<x> = F['x']
                xP = -div[0]
                EL = E.change_ring(L)
                yP = find_y_coordinate(EL,L(xP))
                P = EL(L(xP),yP)
                Q = P
                kernel_poly = (x-xP)
                for k in range(2,ell):
                    Q = Q + P
                    xQ = F(Q[0])
                    if not (x-xQ).divides(kernel_poly):
                        kernel_poly = kernel_poly*(x-xQ)
                        if (x-xQ) in factors:
                            factors.remove(x-xQ)
                kernel_polys.append(kernel_poly)
    edges = {}
    for kernel_poly in kernel_polys:
        phi = EllipticCurveIsogeny(E,kernel_poly)
        phiE = phi.codomain()
        j = phiE.j_invariant()
	if j in edges:
            multiple_edges = edges[j]
            multiple_edges.append(phi)
	    edges[j] = multiple_edges
	else:
            edges[j] = [phi]
    return edges


def torsion_gens(E,ell):
    """
    Computes a basis of the ell-torsion of E, where ell is a prime number.

    The output is P, Q,  E', iota where E' over L is the base change of E to a field extension L over F such that
    E(L) contains E[ell]. The points P and Q generate E[ell]. iota is the embedding of F into L used for
    base changing E over F to E over L.
    """

    from sage.rings.finite_rings.hom_finite_field import FiniteFieldHomomorphism_generic
    import random
    p = E.base_field().characteristic()
    base_degree = E.base_field().degree()
    F = GF(p^(base_degree))
    coerce_base_field = FiniteFieldHomomorphism_generic(Hom(E.base_field(),F))
    E_over_F = coerce_curve(E,coerce_base_field)
    psi = E_over_F.division_polynomial(ell)
    factors = psi.factor()
    f = factors[0][0]
    d = f.degree()
    K = GF(p^(d*base_degree))
    L = GF(p^(2*d*base_degree))
    embed_F_to_K = FiniteFieldHomomorphism_generic(Hom(F,K))
    embed_K_to_L = FiniteFieldHomomorphism_generic(Hom(K,L))
    new_factors = coerce_poly(f, embed_F_to_K).factor()
    xP = -new_factors[0][0][0]
    E_over_L = coerce_curve(E_over_F, (embed_K_to_L)*(embed_F_to_K))
    xP = embed_K_to_L(xP)
    yP = find_y_coordinate(E_over_L, xP)
    P = E_over_L(xP,yP)
    Q = P
    while P.weil_pairing(Q,ell) == 1:
        f = random.choice(list(factors))[0]
        newK = GF(p^(base_degree*f.degree()))
        newL = GF(p^(2*base_degree*f.degree()))
        compositum_degree = lcm(L.degree(), newL.degree())
        compositum = GF(p^(compositum_degree))
        embed_F_to_newK = FiniteFieldHomomorphism_generic(Hom(F,newK))
        embed_newK_to_compositum = FiniteFieldHomomorphism_generic(Hom(newK,compositum))
        E_over_compositum = coerce_curve(E_over_F,(embed_newK_to_compositum)*(embed_F_to_newK))
        new_factors = coerce_poly(f, embed_F_to_newK).factor()
        xQ = -(random.choice(list(new_factors))[0][0])
        xQ = embed_newK_to_compositum(xQ)
        yQ = find_y_coordinate(E_over_compositum,xQ)
        Q = E_over_compositum(xQ,yQ)
        P = E_over_compositum(xP,yP)
    return P, Q, E_over_compositum, (embed_newK_to_compositum)*(embed_F_to_newK)*(coerce_base_field)

def coerce_poly(f, iota):
    R = iota.codomain()[x]
    g = R(0)
    for k in range(f.degree()+1):
        g = g + iota(f[k])*R(x^k)
    return g

def coerce_curve(E, iota):
    E = EllipticCurve([iota(a) for a in E.a_invariants()])
    return E




def trace_of_chain(chain):
    """
    Given a chain of isogenies in G(p,ell) representing an endomorphism phi, computes the trace of phi.

    First we find a list of primes q1,...,qk such that q1*...*qk > 2*(deg phi)^(1/2).
    Then for each prime qj, we compute the trace of phi mod qj with trace_mod_m.
    Then we recover the trace with generalCRT.
    """
    p = chain[0].domain().base_field().characteristic()
    ell = chain[0].degree()
    e = len(chain)
    N = 3
    moduli = [3]
    traces = []
    q = 3
    while N < 2*sqrt(float(ell^e)):
        q = next_prime(q);
        if q != p:
            N = N*q
            moduli.append(q)
    for M in moduli:
        traces.append(trace_mod_prime(M, chain))
    trace = general_CRT(traces, moduli)
    if trace > N/2:
        return trace - N
    else:
        return trace

def trace_mod_prime(M, chain):
    """
    Computes the trace mod M of alpha, where M is a prime not equal to 2,p.

    Let phi = phi_e-1 * ... * phi_0, where phi_k is chain[k]. We compute the trace of phi modulo M
    by computing generators P1,P2 of E[M]
    and checking whether phi^2(P_i) - [t]phi(P_i) + [degphi]P_i = 0 holds on E[m]. if so, return t.
    """

    E = chain[0].domain()
    if chain[len(chain)-1].codomain() != E:
        raise ValueError, 'Chain does not represent an endomorphism'
    degree = 1
    for phi in chain:
        degree = degree*phi.degree()
    R = test_point(E)
    phiR = evaluate_chain(chain,R)
    P, Q, newE, embedding = torsion_gens(E,M)
    new_chain = base_change_chain(chain, embedding)
    flag = (evaluate_chain(new_chain,coerce_point(R, newE, embedding)) == coerce_point(phiR, newE, embedding))
    phiP = evaluate_chain(new_chain, P)
    phiQ = evaluate_chain(new_chain, Q)
    phiphiP = evaluate_chain(new_chain, phiP)
    phiphiQ = evaluate_chain(new_chain, phiQ)
    degM = (degree)%M
    for k in range(M):
        if phiphiP - k*phiP + degM*P == newE(0):
            if phiphiQ - k*phiQ + degM*Q == newE(0):
                if flag:
                    return k
                else:
                    return -k

def general_CRT(values,moduli):
    """
    Given coprime moduli m_1,...,m_n and values a_1,... a_n, this returns x such that x mod m_k = a_k for each k.
    """
    x = values[0]
    M = moduli[0]
    for k in range(1, len(values)):
        x = crt(x, values[k], M, moduli[k])
        M = M*moduli[k]
    return x


def path_to_chain(path,Gpell):
    """
    Returns a chain of isogenies between the vertices in path in the graph Gpell.

    The domain of phi_k is the codomain of phi_{k-1}. The purpose of this is that if G(p,ell)
    is constructed from isogeny_graph( ... ), domains and codomains of edges
    don't agree always.
    """
    p = path[0].parent().characteristic()
    F = GF(p^2)
    R = F['x']
    chain = []
    for k in range(len(path)-1):
        E = Gpell[path[k]]['curve']
        phi = Gpell[path[k]]['neighbors'][path[k+1]][0]
        phiE = Gpell[path[k+1]]['curve']
        f = phi.kernel_polynomial()
        f = R(f)
        phi = EllipticCurveIsogeny(E,f,phiE)
        chain.append(phi)
    return chain



def dual_chain(chain):
    dualChain = []
    for phi in chain:
        dualChain.insert(0,phi.dual())
    return dualChain

def find_y_coordinate(E,xP):
    """
    Computes yP such that (xP,yP) is a point P of E, if such a yP exists.
    """

    R.<y> = (E.base_field())['y']
    a1,a2,a3,a4,a6 = E.a_invariants()
    G = y^2 +(a1*xP+a3)*y-xP^3-a2*xP^2-a4*xP-a6
    factor = G.factor()[0][0]
    if factor.degree()>1:
        raise ValueError, 'Point is not defined over ',E.base_field()
    else:
        return -factor[0]



def evaluate_chain(chain,P):
    """
    Evaluates the isogeny chain at a point P.
    """

    Q = P
    for phi in chain:
        Q = phi(Q)
    return Q

def base_change_chain(chain,iota):
    """
    This coerces a chain of isogenies using the field embedding iota.

    The input chain is a sequence of isogenies defined over a field F, and iota: F to L is a field embedding.
    The output basechange(chain,iota) returns the same chain of isogenies but now they can be evaluated at points
    defined over L. We use this to evaluate endomorphisms
    at points of E[m] which may not be defined over base field of E.
    """

    new_chain = []
    for k in range(len(chain)):
        domain = coerce_curve(chain[k].domain(),iota)
        codomain = coerce_curve(chain[k].codomain(),iota)
        kerPoly = coerce_poly(chain[k].kernel_polynomial(),iota)
        new_chain.append(EllipticCurveIsogeny(domain,kerPoly,codomain))
    return new_chain

def coerce_point(P,E,iota):
    """
    Coerces a point P onto E using iota.

    Here, iota is an embedding of a field F into an extension K. E is the base change to K of a curve E' over F,
    and P is a point on E'. The embedding iota is used to coerce the coordinates of P.
    """

    P = E(iota(P[0]),iota(P[1]))
    return P

def test_point(E):
    P = E.random_point()
    while 2*P == E(0):
        P = E.random_point()
    return P

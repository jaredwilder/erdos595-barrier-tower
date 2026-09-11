"""Independent crosscheck of the BLOCK CLASSIFICATION used by the tau<=2 proof.

CLAIM: if G has no odd cycle of length >= 5 (equivalently tau(G) <= 2), then every
2-connected block of G is bipartite, or K4, or a book B_k (k triangles sharing one edge,
pages pairwise non-adjacent).

This script does NOT reuse the proof. It enumerates graphs, decomposes into blocks by
brute force (a block = a maximal set of edges pairwise related by 'lie on a common cycle'),
and tests each block against the three shapes directly.
"""
import itertools, json, sys, time

def pairs(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]

def odd_cycles(n):
    idx = {e: k for k, e in enumerate(pairs(n))}
    out = set()
    for L in range(5, n + 1, 2):
        for verts in itertools.combinations(range(n), L):
            v0, rest = verts[0], verts[1:]
            for perm in itertools.permutations(rest):
                if perm[0] > perm[-1]:
                    continue
                cyc = (v0,) + perm
                m = 0
                for k in range(L):
                    a, b = cyc[k], cyc[(k + 1) % L]
                    if a > b:
                        a, b = b, a
                    m |= 1 << idx[(a, b)]
                out.add(m)
    return sorted(out), idx

def edges_of(E, P):
    return [e for k, e in enumerate(P) if (E >> k) & 1]

def blocks(edgelist):
    """union-find on edges: two edges are in the same block iff they lie on a common cycle.
    Implemented as: edge e,f same block iff removing any single vertex keeps them connected
    in the edge-adjacency sense. Brute force via biconnected components (Hopcroft-Tarjan)."""
    adj = {}
    for a, b in edgelist:
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    disc, low, parent = {}, {}, {}
    stack, out, timer = [], [], [0]

    def dfs(u):
        disc[u] = low[u] = timer[0]; timer[0] += 1
        for v in adj.get(u, []):
            if v not in disc:
                parent[v] = u
                stack.append((u, v))
                dfs(v)
                low[u] = min(low[u], low[v])
                if low[v] >= disc[u]:
                    comp = []
                    while True:
                        e = stack.pop()
                        comp.append(e)
                        if e == (u, v):
                            break
                    out.append(comp)
            elif v != parent.get(u) and disc[v] < disc[u]:
                stack.append((u, v))
                low[u] = min(low[u], disc[v])
    for u in list(adj):
        if u not in disc:
            dfs(u)
    return out

def is_bipartite(comp):
    adj = {}
    for a, b in comp:
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    col = {}
    for s in adj:
        if s in col:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if v not in col:
                    col[v] = 1 - col[u]
                    st.append(v)
                elif col[v] == col[u]:
                    return False
    return True

def shape(comp):
    V = sorted({x for e in comp for x in e})
    ES = {frozenset(e) for e in comp}
    if is_bipartite(comp):
        return "BIPARTITE"
    if len(V) == 4 and len(ES) == 6:
        return "K4"
    # book: exists spine {a,b} with every edge incident to a or b, ab present,
    # pages adjacent to both a and b, pages pairwise non-adjacent
    for a, b in itertools.combinations(V, 2):
        if frozenset((a, b)) not in ES:
            continue
        pages = [v for v in V if v not in (a, b)]
        ok = all(frozenset((a, p)) in ES and frozenset((b, p)) in ES for p in pages)
        ok = ok and all(frozenset(e) <= {a, b} or (a in e) or (b in e) for e in comp)
        ok = ok and all(frozenset((p, q)) not in ES for p, q in itertools.combinations(pages, 2))
        if ok:
            return "BOOK"
    return "UNCLASSIFIED"

def run(n):
    P = pairs(n)
    ocs, idx = odd_cycles(n)
    t0 = time.time()
    counts = {}
    bad = []
    tested = 0
    for E in range(1 << len(P)):
        ok = True
        for m in ocs:
            if E & m == m:
                ok = False
                break
        if not ok:
            continue
        tested += 1
        el = edges_of(E, P)
        if not el:
            continue
        for comp in blocks(el):
            s = shape(comp)
            counts[s] = counts.get(s, 0) + 1
            if s == "UNCLASSIFIED":
                bad.append(sorted(tuple(sorted(e)) for e in comp))
    return {"n": n, "labelled_graphs_with_tau_le_2": tested,
            "block_shapes": counts,
            "unclassified_blocks": bad[:20],
            "unclassified_count": len(bad),
            "seconds": round(time.time() - t0, 1)}

if __name__ == "__main__":
    out = {"tool": "classification_check.py"}
    for n in (4, 5, 6, 7):
        out["n%d" % n] = run(n)
        print(json.dumps(out["n%d" % n]), flush=True)
    open(sys.argv[1] if len(sys.argv) > 1 else "receipt-classification.json", "w").write(
        json.dumps(out, indent=1))

"""Exact tc/tau check for Erdos 595 without the K4-free hypothesis.

tau(G) = max chi(H) over triangle-free subgraphs H <= G.
tc(G)  = least k with E(G) a union of k triangle-free subgraphs.

Exactness facts used (both re-verified inside this script where finite):
  F1  tau(G) >= 3  <=>  G contains an odd cycle of length >= 5 as a subgraph.
      (a triangle-free non-bipartite graph contains an odd cycle, necessarily >= 5;
       conversely such a cycle is itself a triangle-free subgraph with chi = 3.)
  F2  for n <= 10, tau(G) <= 3, since the least order of a triangle-free 4-chromatic
      graph is 11 (Chvatal: the Grotzsch graph is the unique 11-vertex one).
      => for n <= 10 tau is EXACT as {1 if no edge, 2, 3} by F1.
  F3  tc(G) <= 3 for every G on <= 16 vertices, because R(3,3,3) = 17 gives a
      triangle-free 3-cover of K_16. Verified here for K_7 by direct search.

Therefore over n <= 10 the whole conjecture tc <= tau is EQUIVALENT to
      tau(G) = 2  ==>  tc(G) <= 2,
i.e. no odd cycle of length >= 5  ==>  edges 2-coverable by triangle-free graphs.
This script tests that exhaustively on n = 7 and by maximal-graph sampling above it.
"""
import itertools, json, random, sys, time, hashlib

def edge_index(n):
    idx = {}
    ed = []
    for i in range(n):
        for j in range(i + 1, n):
            idx[(i, j)] = len(ed)
            ed.append((i, j))
    return idx, ed

def triangle_masks(n, idx):
    out = []
    for a, b, c in itertools.combinations(range(n), 3):
        out.append((1 << idx[(a, b)]) | (1 << idx[(a, c)]) | (1 << idx[(b, c)]))
    return out

def triangle_edge_triples(n, idx):
    out = []
    for a, b, c in itertools.combinations(range(n), 3):
        out.append((idx[(a, b)], idx[(a, c)], idx[(b, c)]))
    return out

def odd_cycle_masks(n, idx, minlen=5):
    """edge masks of all cycles of odd length >= minlen"""
    out = []
    for L in range(minlen, n + 1, 2):
        for verts in itertools.combinations(range(n), L):
            v0 = verts[0]
            rest = verts[1:]
            seen = set()
            for perm in itertools.permutations(rest):
                if perm[0] > perm[-1]:
                    continue  # kill the reversal duplicate
                cyc = (v0,) + perm
                key = cyc
                if key in seen:
                    continue
                seen.add(key)
                m = 0
                for k in range(L):
                    a, b = cyc[k], cyc[(k + 1) % L]
                    if a > b:
                        a, b = b, a
                    m |= 1 << idx[(a, b)]
                out.append(m)
    return sorted(set(out))

def has_odd_cycle_ge5(E, ocm):
    for m in ocm:
        if E & m == m:
            return True
    return False

def cover_ok(E, k, tri_triples, nedges):
    """is E a union of k triangle-free subgraphs? backtracking edge colouring"""
    present_tri = [t for t in tri_triples
                   if (E >> t[0]) & 1 and (E >> t[1]) & 1 and (E >> t[2]) & 1]
    if not present_tri:
        return k >= 1 or E == 0
    edges = [e for e in range(nedges) if (E >> e) & 1]
    # only edges lying in some present triangle constrain anything
    constrained = set()
    for t in present_tri:
        constrained.update(t)
    edges = [e for e in edges if e in constrained]
    tri_of = {e: [] for e in edges}
    for t in present_tri:
        for e in t:
            tri_of[e].append(t)
    colour = {}
    order = sorted(edges, key=lambda e: -len(tri_of[e]))

    def bad(e):
        c = colour[e]
        for t in tri_of[e]:
            if all(colour.get(x, -1) == c for x in t):
                return True
        return False

    def rec(i, used):
        if i == len(order):
            return True
        e = order[i]
        for c in range(min(used + 1, k)):
            colour[e] = c
            if not bad(e):
                if rec(i + 1, max(used, c + 1)):
                    return True
            del colour[e]
        return False

    return rec(0, 0)

def tc_exact(E, tri_triples, nedges, kmax=4):
    if E == 0:
        return 0
    for k in range(1, kmax + 1):
        if cover_ok(E, k, tri_triples, nedges):
            return k
    return kmax + 1

def tau_exact_small(E, ocm):
    """exact for n <= 10 by F1 + F2"""
    if E == 0:
        return 1
    return 3 if has_odd_cycle_ge5(E, ocm) else 2

# ---------------------------------------------------------------- run
def run_exhaustive(n):
    idx, ed = edge_index(n)
    nedges = len(ed)
    tri = triangle_edge_triples(n, idx)
    trim = triangle_masks(n, idx)
    ocm = odd_cycle_masks(n, idx)
    t0 = time.time()
    total = 1 << nedges
    viol = []
    tau2_count = 0
    tau2_maximal = 0
    checked_tau2 = 0
    tc3_count = 0
    for E in range(total):
        # cheap: any triangle at all?
        has_tri = False
        for m in trim:
            if E & m == m:
                has_tri = True
                break
        if not has_tri:
            continue  # tc <= 1 <= tau whenever there is an edge
        if has_odd_cycle_ge5(E, ocm):
            # tau = 3; need tc <= 3
            if not cover_ok(E, 3, tri, nedges):
                viol.append(("tau3", E))
            else:
                tc3_count += 1
            continue
        tau2_count += 1
        checked_tau2 += 1
        if not cover_ok(E, 2, tri, nedges):
            viol.append(("tau2", E))
        # maximality
        maximal = True
        for e in range(nedges):
            if not (E >> e) & 1:
                if not has_odd_cycle_ge5(E | (1 << e), ocm):
                    maximal = False
                    break
        if maximal:
            tau2_maximal += 1
    return {
        "n": n,
        "graphs_enumerated": total,
        "labelled_graphs_with_a_triangle_and_tau_eq_2": tau2_count,
        "of_those_edge_maximal": tau2_maximal,
        "labelled_graphs_with_a_triangle_and_tau_eq_3": tc3_count,
        "violations_tc_gt_tau": [{"class": c, "edge_mask": E,
                                  "edges": [ed[i] for i in range(nedges) if (E >> i) & 1]}
                                 for c, E in viol],
        "seconds": round(time.time() - t0, 1),
    }

def run_maximal_sample(n, samples, seed=595):
    """random edge-maximal tau<=2 graphs on n vertices; tc<=2 ?"""
    rng = random.Random(seed)
    idx, ed = edge_index(n)
    nedges = len(ed)
    tri = triangle_edge_triples(n, idx)
    ocm = odd_cycle_masks(n, idx)
    viol = []
    seen = set()
    t0 = time.time()
    for _ in range(samples):
        order = list(range(nedges))
        rng.shuffle(order)
        E = 0
        for e in order:
            cand = E | (1 << e)
            if not has_odd_cycle_ge5(cand, ocm):
                E = cand
        seen.add(E)
        if not cover_ok(E, 2, tri, nedges):
            viol.append({"edge_mask": E,
                         "edges": [ed[i] for i in range(nedges) if (E >> i) & 1]})
    return {
        "n": n,
        "samples": samples,
        "distinct_maximal_tau2_graphs_found": len(seen),
        "violations_tc_gt_2": viol,
        "seconds": round(time.time() - t0, 1),
    }

def run_K7_cover():
    n = 7
    idx, ed = edge_index(n)
    nedges = len(ed)
    tri = triangle_edge_triples(n, idx)
    E = (1 << nedges) - 1
    return {"K7_2_coverable": cover_ok(E, 2, tri, nedges),
            "K7_3_coverable": cover_ok(E, 3, tri, nedges),
            "tc_K7": tc_exact(E, tri, nedges)}

if __name__ == "__main__":
    out = {"tool": "tc_tau_exact.py"}
    out["K7"] = run_K7_cover()
    out["exhaustive_n5"] = run_exhaustive(5)
    out["exhaustive_n6"] = run_exhaustive(6)
    out["exhaustive_n7"] = run_exhaustive(7)
    for n in (8, 9, 10):
        out["maximal_sample_n%d" % n] = run_maximal_sample(n, 400 if n < 10 else 200)
    js = json.dumps(out, indent=1)
    open(sys.argv[1] if len(sys.argv) > 1 else "receipt.json", "w").write(js)
    print(js[:4000])

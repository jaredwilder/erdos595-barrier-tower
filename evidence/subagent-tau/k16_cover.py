"""Verify tc(K_16) <= 3 by EXHIBITING the cover, not by citing R(3,3,3) = 17.

Vertices = GF(16) built as F_2[x]/(x^4+x+1). The multiplicative group is cyclic of
order 15; H = the subgroup of order 5. Colour the edge {u,v} by which coset of H the
difference u+v lies in. Each colour class is checked triangle-free by brute force over
all 560 vertex triples, and the three classes are checked to partition E(K_16).

Consequence used downstream: tc(G) <= 3 for EVERY graph on at most 16 vertices, since
tc is monotone under subgraphs.
"""
import itertools, json, sys

MOD = 0b10011  # x^4 + x + 1

def mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a & 0b10000:
            a ^= MOD
    return r

def powg(g, k):
    r = 1
    for _ in range(k):
        r = mul(r, g)
    return r

def main():
    g = 2  # x is primitive for x^4+x+1
    order = 1
    t = g
    while t != 1:
        t = mul(t, g)
        order += 1
    assert order == 15, order
    H = {powg(g, 3 * i) for i in range(5)}
    cosets = [H,
              {mul(g, h) for h in H},
              {mul(mul(g, g), h) for h in H}]
    assert len(set().union(*cosets)) == 15
    assert all(len(c) == 5 for c in cosets)

    V = list(range(16))
    colour = {}
    for u, v in itertools.combinations(V, 2):
        d = u ^ v
        c = [i for i, S in enumerate(cosets) if d in S]
        assert len(c) == 1
        colour[(u, v)] = c[0]

    mono = []
    for a, b, c in itertools.combinations(V, 3):
        cols = {colour[(a, b)], colour[(a, c)], colour[(b, c)]}
        if len(cols) == 1:
            mono.append((a, b, c))

    sizes = [sum(1 for e in colour if colour[e] == i) for i in range(3)]
    out = {
        "tool": "k16_cover.py",
        "field": "GF(16) = F_2[x]/(x^4+x+1), generator x",
        "coset_sizes": [len(c) for c in cosets],
        "edges_total": len(colour),
        "class_sizes": sizes,
        "triples_checked": 560,
        "monochromatic_triangles": len(mono),
        "K16_3_coverable": len(mono) == 0 and sum(sizes) == 120,
        "consequence": "tc(G) <= 3 for every graph on at most 16 vertices",
    }
    print(json.dumps(out, indent=1))
    open(sys.argv[1] if len(sys.argv) > 1 else "receipt-k16.json", "w").write(
        json.dumps(out, indent=1))

main()

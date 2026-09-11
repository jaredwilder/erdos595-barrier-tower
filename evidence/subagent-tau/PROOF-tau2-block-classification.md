# Erdős 595 without the K4-free hypothesis — the τ ≤ 2 case, closed

Notation. `tc(G)` = least cardinal k with E(G) a union of k triangle-free subgraphs.
`τ(G)` = sup of χ(H) over triangle-free H ≤ G. Target: `tc(G) ≤ τ(G)` for every graph,
no K4-free hypothesis.

## 0. Two exact facts that make the small cases decidable

**F1.** τ(G) ≥ 3 ⟺ G contains an odd cycle of length ≥ 5 as a subgraph.
(⇐ such a cycle is itself a triangle-free subgraph with χ = 3. ⇒ a triangle-free
non-bipartite subgraph contains an odd cycle, and it cannot be a triangle.)

**F2.** τ(G) = 2 ⟺ G has an edge and no odd cycle of length ≥ 5.

**F3.** tc(G) ≤ 3 for every G on at most 16 vertices — verified constructively, not cited:
`k16_cover.py` builds the GF(16) coset colouring of K₁₆ and checks all 560 triples,
0 monochromatic. tc is monotone under subgraphs.

**F4.** For n ≤ 10, τ(G) ∈ {1,2,3} exactly, by F1 plus the fact that the least order of a
triangle-free 4-chromatic graph is 11 (Grötzsch/Chvátal).

Consequence — **THE REDUCTION.** On at most 16 vertices, τ ≥ 3 already gives tc ≤ 3 ≤ τ
by F3. So the whole conjecture on ≤ 16 vertices is EQUIVALENT to the single implication

> **(T2)  τ(G) = 2  ⟹  tc(G) ≤ 2.**

## 1. Theorem (T2), proved

**Step 0 — triangles are intra-block.** Any triangle of G lies inside one 2-connected
block, because its three vertices lie on a common cycle. So a triangle-free 2-cover may be
chosen block by block and glued: `tc(G) = max over blocks B of tc(B)`.

**Step 1 — the local structure.** Let B be a 2-connected block of G with τ(G) ≤ 2 and let
{a,b,c} be a triangle in B. Let v ∈ V(B) \ {a,b,c}. By the fan lemma (2-connectivity) there
are two vertex-disjoint paths P, Q from v to {a,b,c}, internally avoiding the triangle,
ending at distinct triangle vertices x ≠ y; write p = |P|, q = |Q| (edge lengths ≥ 1), and
let z be the third triangle vertex. Two cycles exist:

  C₁ = v–P–x–y–Q–v of length p+q+1,  C₂ = v–P–x–z–y–Q–v of length p+q+2.

Exactly one of them is odd. If p+q+2 is odd it has length ≥ 4, hence ≥ 5 — refused by F2.
So p+q+1 is odd, and being an odd cycle it must have length 3, i.e. p = q = 1.

> **Every vertex of B is adjacent to at least two vertices of every triangle of B.**

**Step 2 — one spine.** Suppose v is adjacent to a,b and w ≠ v is adjacent to b,c. Then
a–v–b–w–c–a is a 5-cycle (the edge ca exists): refused. So all vertices outside the
triangle attach to the SAME pair, say {a,b}.

**Step 3 — K4 or a book.** If some v is adjacent to all of a,b,c and another outside w is
adjacent to a,b, then c–v–a–w–b–c is a 5-cycle: refused. Hence either B = K4, or every
outside vertex is adjacent to exactly {a,b}. In the latter case, if two outside pages v,w
were adjacent, v–w–a–c–b–v is a 5-cycle: refused. So B is the book Bₖ: spine ab, pages
pairwise non-adjacent, each joined to both spine ends.

> **CLASSIFICATION. Every block of a graph with τ ≤ 2 is bipartite, K4, or a book Bₖ.**

**Step 4 — each shape has tc ≤ 2.**
- bipartite: G itself is triangle-free, tc ≤ 1.
- book: every edge meets the spine {a,b}; the two stars at a and at b are triangle-free.
- K4: χ(K4) = 4 = 2², so the estate's kernel-checked `erdos595_proper_binary_cover`
  (χ ≤ 2^κ ⟹ tc ≤ κ) gives tc ≤ 2 directly.

∎ (T2). Combined with F3: **tc(G) ≤ τ(G) for EVERY graph on at most 16 vertices, with no
K4-free hypothesis.** Nothing above uses finiteness except Step 0/Step 1's fan lemma, both
of which hold for infinite graphs at finite connectivity, so (T2) holds for arbitrary G.

## 2. What is machine-verified here

| object | tool | receipt |
|---|---|---|
| tc ≤ τ exhaustively, EXACT τ, all 2²¹ labelled graphs on 7 vertices | `tc_tau_exact.py` | `receipt-exhaustive.json` |
| the CLASSIFICATION, independently re-derived by biconnected decomposition | `classification_check.py` | `receipt-classification.json` |
| tc(K₁₆) ≤ 3 by explicit GF(16) cover | `k16_cover.py` | `receipt-k16.json` |
| book case in Lean (two-star cover) | `msl_lean_cable.py` | `oracle/frontier_formalizer/cable/receipts/erdos595-two-star-cover.cable.json` |
| bipartite + book cases in Lean | `msl_lean_cable.py` | `oracle/frontier_formalizer/cable/receipts/erdos595-tau2-block-shapes.cable.json` |

## 3. What is NOT closed

The general conjecture (τ ≥ 4, i.e. graphs on ≥ 17 vertices) is untouched. For complete
graphs it is the comparison tc(Kₙ) ≈ log n against τ(Kₙ) = Θ(√(n/log n)) — true with vast
room — but no argument here covers general large G.

The τ ≤ 2 theorem is NOT fully in Lean: Steps 0 and 1 need block decomposition and the fan
lemma (Menger, k = 2), neither of which appears anywhere in the sealed Erdős-595 library.
That is the exact formalization bottleneck.

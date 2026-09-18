# Erdős #595 — triangle covers and the continuum threshold

For a graph `G`, let `tc(G)` be the least cardinal number of triangle-free subgraphs whose edge sets cover `E(G)`. Erdős #595 asks whether a `K_4`-free graph can satisfy

\[
tc(G)>\aleph_0.
\]

This repository proves the sharp cardinal threshold for the covering problem **without** the `K_4`-free restriction and develops structural consequences for any `K_4`-free witness.

## Every graph of size at most the continuum is countably coverable

If

\[
|V(G)|\le 2^{\aleph_0},
\]

then

\[
\boxed{tc(G)\le\aleph_0.}
\]

The proof injects the vertices into Cantor space. For each edge, use the first binary coordinate at which its endpoints differ. Edges receiving the same coordinate form a bipartite graph, hence a triangle-free layer. Countably many coordinates therefore cover every edge.

This gives an immediate lower bound on the size of any graph with uncountable triangle-cover number: it must have **strictly more than continuum-many vertices**.

## The unrestricted threshold is sharp

Combining the first-difference construction with the Erdős–Rado upper-side obstruction gives the exact unrestricted cardinal transition:

> **Without the `K_4`-free condition, non-countable-coverability begins at the successor of the continuum.**

The formal development also proves two useful reductions for a least witness:

- its cardinality has uncountable cofinality;
- one connected component already carries the full obstruction.

Thus the remaining difficulty in Erdős #595 is genuinely the interaction between very large cardinal structure and `K_4`-freeness, not merely the size of the graph.

## Structural consequences for `K_4`-free graphs

The theorem bank develops several complementary descriptions of triangle-cover number.

Among them:

- exact blocker / triangle-transversal dualities for `tc(G)`;
- the bipartite-cover identity
  \[
  bc(G)=\min\{\kappa:\chi(G)\le 2^\kappa\};
  \]
- countable exact-`\aleph_0` cores extractable from a hypothetical `K_4`-free witness;
- connected, locally finite, one-ended exact-`\aleph_0` cores built from finite Folkman inputs;
- product-colouring and chromatic-dispersion lower bounds;
- an equivalence between `K_4`-freeness of `G` and Berge-`C_3`-freeness of its triangle hypergraph;
- endpoint-representation criteria for triangle hypergraphs;
- explicit finite examples showing that no fixed bound can control how many triangles contain a single edge of a `K_4`-free graph.

The broader fiber/coherence theory related to the same problem is developed in [`triangle-cover-number`](https://github.com/jaredwilder/triangle-cover-number) and [`fiber-coherence-cycle-rank`](https://github.com/jaredwilder/fiber-coherence-cycle-rank).

## Lean verification

[`barrier-tower/theorems/`](barrier-tower/theorems) contains **27 Lean 4 theorem files, all sorry-free**. Their recorded axiom footprint is

```text
{propext, Classical.choice, Quot.sound}
```

and `barrier-tower/INDEX.json` records the per-file SHA-256 hashes and verification summary.

Earlier exploratory files containing `sorry` remain under `evidence/lean/` as historical drafts and are not part of the 27-file theorem set.

## Reading the repository

- `barrier-tower/theorems/` — formal proofs of the continuum threshold and related cardinal reductions;
- `theorem-bank/README.md` — 65 structural theorem statements and proof notes;
- `evidence/` — finite certificates, literature notes, formalization receipts, and research history.

The cardinal threshold theorem is the cleanest entry point: **continuum-sized graphs are always countably triangle-coverable; the open issue is whether the added `K_4`-free condition can coexist with an obstruction above that threshold.**

Author: Jared Wilder.  
License: Apache-2.0.
# Erdős 595: triangle-cover structure and the continuum barrier

A focused repository for Jared Wilder's work on Erdős Problem #595: triangle-cover number, cardinal barriers, formal verification, finite obstructions, and structural reformulations.

The repository now combines two previously separated research lanes:

1. a **27-file sorry-free Lean barrier package** proving the sharp cardinal coverability threshold and related witness structure;
2. a recovered **65-card triangle-cover theorem bank** containing dualities, compactness/core extraction, chromatic-dispersion machinery, triangle-hypergraph structure, and preserved negative results.

## The problem

For a graph `G`, let `tc(G)` be the least cardinal number of triangle-free subgraphs whose edge sets cover `E(G)`.

Erdős #595 asks whether there exists a `K4`-free graph with `tc(G)>aleph_0`.

## Formal continuum barrier

The formal package proves:

- **Every graph on at most continuum-many vertices is coverable by countably many triangle-free graphs.** Inject the vertices into Cantor space and colour each edge by the least coordinate where its endpoints differ; three sequences cannot pairwise differ at one fixed coordinate.
- **Without the `K4`-free restriction, non-coverability begins exactly at the successor of the continuum.** Erdős–Rado forces a monochromatic triangle in every countable colouring of pairs there, while the Cantor-space colouring proves the lower side.
- **The least witness size has uncountable cofinality.** A countable-cofinality cardinal splits into countably many smaller parts, whose covers can be combined.
- **A witness occurs inside one connected component.** Coverability is preserved under arbitrary disjoint unions.

Thus the cardinal threshold itself is sharp; the remaining flagship difficulty is whether the additional `K4`-free condition can coexist with non-coverability.

## Recovered theorem bank

[`theorem-bank/README.md`](theorem-bank/README.md) promotes a second substantial #595 research packet that had been buried in the general intake archive.

Its **65 theorem cards** include:

- exact blocker / triangle-transversal centeredness dualities for `tc(G)`;
- the exact bipartite-cover relation `bc(G)=min{kappa: chi(G)<=2^kappa}`;
- cofinality restrictions on minimal witnesses;
- extraction of a countable `K4`-free exact-`aleph_0` core from any hypothetical witness;
- connected, locally finite, one-ended exact-`aleph_0` cores from finite Folkman inputs;
- product-coloring and chromatic-dispersion lower bounds;
- the equivalence between `K4`-freeness of `G` and Berge-`C3`-freeness of `Tri(G)`;
- exact endpoint-representation criteria for triangle hypergraphs and finite NP membership for realizability;
- an explicit refutation of any fixed triangle-multiplicity bound on an edge in finite `K4`-free graphs.

The original exact ledger remains public in `jaredwilder/unpublished-math-papers/erdos595-triangle-cover/` as provenance. This repository is now the preferred problem-level reading surface.

## Formal verification

`barrier-tower/theorems/` contains **27 Lean 4 files, all sorry-free**, checked with Lean v4.31.0-rc1. Their axiom footprint is exactly `{propext, Classical.choice, Quot.sound}`.

`barrier-tower/INDEX.json` records per-file SHA-256 values and the verification summary.

`evidence/lean/` separately preserves seven earlier exploratory files containing `sorry` (`Compactness`, `Continuum`, `Countable`, `Dispersion`, `Hom`, `Stability`, `Transversal`). They are historical drafts rather than part of the 27-file theorem package.

## Evidence archive

`evidence/` contains roughly 200 supporting files, including a Paley-17 certificate separating two finite invariants, formalization receipts, literature notes, and research logs.

The theorem-bank source statuses remain distinct from formal verification status and from literature novelty. Each result should be cited at the strongest evidence level actually available for that result.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## License

Apache-2.0.

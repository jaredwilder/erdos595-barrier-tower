# Erdős #595 — Triangle Covers and the Continuum Barrier

**Jared Wilder**

Formal and structural work on Erdős Problem #595: triangle-cover number, cardinal thresholds, finite obstructions, and `K4`-free structure.

This repository combines two major research packages:

1. a **27-file sorry-free Lean development** proving a sharp cardinal coverability threshold and related witness structure;
2. a **65-card theorem bank** covering dualities, compactness and core extraction, chromatic-dispersion machinery, triangle-hypergraph structure, and finite obstructions.

## The problem

For a graph `G`, let `tc(G)` be the least cardinal number of triangle-free subgraphs whose edge sets cover `E(G)`.

Erdős #595 asks whether there exists a `K4`-free graph with `tc(G) > aleph_0`.

## Formal continuum barrier

The Lean package proves:

- **Every graph on at most continuum-many vertices is coverable by countably many triangle-free graphs.** Inject the vertices into Cantor space and color each edge by the least coordinate where its endpoints differ.
- **Without the `K4`-free restriction, non-coverability begins exactly at the successor of the continuum.** Erdős–Rado gives the upper-side obstruction; the Cantor-space coloring gives the lower side.
- **The least witness size has uncountable cofinality.**
- **A witness occurs inside one connected component.**

The cardinal threshold is therefore sharp. The unresolved core is the interaction with the additional `K4`-free condition.

## Structural theorem bank

[`theorem-bank/README.md`](theorem-bank/README.md) contains 65 theorem cards, including:

- exact blocker / triangle-transversal dualities for `tc(G)`;
- the bipartite-cover identity `bc(G)=min{kappa : chi(G)<=2^kappa}`;
- cofinality restrictions on minimal witnesses;
- extraction of countable `K4`-free exact-`aleph_0` cores from hypothetical witnesses;
- connected, locally finite, one-ended exact-`aleph_0` cores from finite Folkman inputs;
- product-coloring and chromatic-dispersion lower bounds;
- the equivalence between `K4`-freeness of `G` and Berge-`C3`-freeness of `Tri(G)`;
- endpoint-representation criteria for triangle hypergraphs;
- an explicit refutation of any fixed triangle-multiplicity bound on an edge in finite `K4`-free graphs.

## Formal verification

`barrier-tower/theorems/` contains **27 Lean 4 files, all sorry-free**, checked with Lean v4.31.0-rc1. Their axiom footprint is exactly `{propext, Classical.choice, Quot.sound}`.

`barrier-tower/INDEX.json` records per-file SHA-256 hashes and the verification summary.

Earlier exploratory files containing `sorry` are retained under `evidence/lean/` as historical drafts and are not part of the 27-file theorem package.

## Evidence archive

`evidence/` contains roughly 200 supporting files: finite certificates, formalization receipts, literature notes, and research logs. The original theorem ledger also remains available in `jaredwilder/unpublished-math-papers/erdos595-triangle-cover/`.

**First public timestamp:** 2026-09-10  
**License:** Apache-2.0
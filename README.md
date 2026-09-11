# Erdős 595: a sharp continuum coverability barrier

A formalized barrier theorem for Erdős 595: **every graph on at most continuum-many vertices is coverable by countably many triangle-free graphs; non-coverability begins exactly at the successor of the continuum; the least witness cardinal has uncountable cofinality; and a witness may be taken inside one connected component.**

The theorem package is implemented in **27 sorry-free Lean 4 files** with Mathlib's standard classical axiom footprint.

Author: Jared Wilder. First public timestamp: 2026-09-10. Work dated 2026-09-05.

## The problem

> Is there an infinite graph `G` containing no `K4` that is not the union of countably many triangle-free graphs?

## Barrier theorem

Call a graph *coverable* if it is the union of countably many triangle-free graphs.

- **Every graph on at most continuum-many vertices is coverable.** Inject the vertices into Cantor space and colour each edge by the least coordinate where its endpoints differ; three sequences cannot pairwise differ at one fixed coordinate.
- **Non-coverable graphs begin exactly at the successor of the continuum.** Erdős–Rado forces a monochromatic triangle in every countable colouring of the pairs there, while the Cantor-space colouring proves the lower side of the threshold.
- **The least witness size has uncountable cofinality.** A countable-cofinality cardinal splits into countably many smaller parts, whose covers can be combined.
- **A witness occurs inside one connected component.** Coverability is preserved under arbitrary disjoint unions.

Together these results isolate the remaining question: can non-coverability still occur after imposing the additional `K4`-free condition?

## Formal verification

`barrier-tower/theorems/` contains **27 Lean 4 files, all sorry-free**, checked with Lean v4.31.0-rc1. Their axiom footprint is exactly `{propext, Classical.choice, Quot.sound}`.

`barrier-tower/INDEX.json` records per-file SHA-256 values and the verification summary.

`evidence/lean/` separately preserves seven earlier exploratory files containing `sorry` (`Compactness`, `Continuum`, `Countable`, `Dispersion`, `Hom`, `Stability`, `Transversal`). They are historical drafts rather than part of the 27-file theorem package.

## Additional material

`evidence/` contains roughly 200 supporting files, including a Paley-17 certificate separating two finite invariants, formalization receipts, literature notes, and research logs.

## License

Apache-2.0.
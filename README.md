# erdos595-barrier-tower

**A kernel-sealed barrier theorem for Erdős 595:** every graph on at most continuum-many vertices is
coverable by countably many triangle-free graphs, non-coverability begins exactly at the successor
of the continuum, the least witness cardinal has uncountable cofinality, and a witness can be taken
inside one connected component.

The sealed tower is implemented in **27 sorry-free Lean 4 files** with the standard classical axiom
footprint.

Author: Jared Wilder. First public timestamp: 2026-09-10. Work dated 2026-09-05.

## The problem

> Is there an infinite graph G which contains no K4 and is not the union of countably many
> triangle-free graphs?

Contract sha256 `7a511a911acc0ece511b59d5048818b5073983519f93103d6c1dbe79da8eb794`.

## Barrier theorem

Call a graph *coverable* if it is the union of countably many triangle-free graphs.

- **Every graph on at most continuum-many vertices is coverable.** Inject the vertices into Cantor
  space and colour each edge by the least coordinate where its endpoints differ; three sequences
  cannot pairwise differ at one fixed coordinate.
- **Non-coverable graphs begin exactly at the successor of the continuum.** There Erdős–Rado
  forces a monochromatic triangle in every countable colouring of the pairs, so the complete graph
  on that cardinal is not coverable; the Cantor-space colouring shows the threshold is sharp.
- **The least witness size has uncountable cofinality.** A countable-cofinality cardinal splits into
  countably many smaller parts and their covers reassemble.
- **A witness lives inside one connected component.** Coverability survives disjoint unions of
  arbitrary size.

These results isolate the remaining Erdős 595 difficulty sharply: whether the phenomenon that begins
at the successor of the continuum can still occur after imposing the `K4`-free condition.

## Scope

The repository proves the barrier theorem and necessary conditions above. It does not construct a
`K4`-free non-coverable graph or prove that none exists. That is the exact remaining seam, stated
after the mathematics rather than in place of it.

## Verification

`barrier-tower/theorems/` holds **27 Lean 4 files, every one sorry-free**, Lean v4.31.0-rc1,
`lake env lean` exit 0, axiom footprint exactly `{propext, Classical.choice, Quot.sound}`.
`barrier-tower/INDEX.json` carries a per-file SHA-256 and reports 0 unclean.

`evidence/lean/` separately preserves 7 earlier exploratory files that do contain `sorry`
(Compactness, Continuum, Countable, Dispersion, Hom, Stability, Transversal). They are historical
drafts and are not part of the sealed theorem tower.

## Also here

`evidence/` carries roughly 200 files: the C17 certificate and splits (a Paley graph of order 17
separating two invariants), cable receipts, literature probes, and the campaign logs.

## License

Apache-2.0.

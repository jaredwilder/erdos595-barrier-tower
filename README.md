# erdos595-barrier-tower

A kernel-sealed tower of **necessary conditions** on any witness to Erdos problem 595, plus the
algebra of the class such a witness must escape.

Author: Jared Wilder. First public timestamp: 2026-09-10. Work dated 2026-09-05.

## The problem, frozen

> Is there an infinite graph G which contains no K4 and is not the union of countably many
> triangle-free graphs?

Contract sha256 `7a511a911acc0ece511b59d5048818b5073983519f93103d6c1dbe79da8eb794`.

## Status: NOT CLOSED

**No witness constructed. No refutation proved.** That sentence is from the run's own report and it
is the first thing the report says.

## What was actually proved

Call a graph *coverable* if it is the union of countably many triangle-free graphs.

- **Every graph on at most continuum-many vertices is coverable.** Inject the vertices into Cantor
  space and colour each edge by the least coordinate where its endpoints differ; three sequences
  cannot pairwise differ at one fixed coordinate.
- **Non-coverable graphs begin exactly at the successor of the continuum.** There Erdos-Rado forces
  a monochromatic triangle in every countable colouring of the pairs, so the complete graph on that
  cardinal is not coverable, and the colouring above shows the threshold is sharp.
- **The least witness size has uncountable cofinality.** A countable-cofinality cardinal splits into
  countably many smaller parts and their covers reassemble.
- **A witness lives inside one connected component.** Coverability survives disjoint unions of
  arbitrary size.

So Erdos 595 asks precisely whether the phenomenon that begins at the successor of the continuum
survives deleting every K4. Every source of non-coverability this work can name runs through large
complete subgraphs, which is exactly what the hypothesis removes. That is the barrier, stated as a
barrier rather than as progress toward a proof.

## Verification

`barrier-tower/theorems/` holds **27 Lean 4 files, every one sorry-free**, Lean v4.31.0-rc1,
`lake env lean` exit 0, axiom footprint exactly `{propext, Classical.choice, Quot.sound}`.
`barrier-tower/INDEX.json` carries a per-file sha256 and reports 0 unclean.

**A deliberate exception, so nobody is misled by a single number:** `evidence/lean/` holds 7 earlier
exploratory files that **do** contain `sorry` (Compactness, Continuum, Countable, Dispersion, Hom,
Stability, Transversal). They are earlier drafts, they are shipped because the working record is the
point, and they are not part of the sealed tower.

## Also here

`evidence/` carries roughly 200 files: the C17 certificate and splits (a Paley graph of order 17
separating two invariants), cable receipts, literature probes, and the campaign logs.

## License

Apache-2.0.

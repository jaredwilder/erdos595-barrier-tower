# Pure Graph-Mathematics Extract from the Three-Way Recursive Forge

**Author:** Jared Wilder  
**Public release:** 2026-09-10

Two standalone Erdős #595 lemmas were recovered from the `three-way-recursive` domain. The surrounding research-system material is not needed for either statement and is not released here.

## Common Omitted-Edge Stable Book Theorem

Let `G` be K4-free with

\[
tc(G)>\aleph_0,
\]

where `tc(G)` is the least number of triangle-free subgraphs whose union covers `G`.

For every countable family `(H_n)` of maximal spanning triangle-free subgraphs of `G`, there is an edge `xy` omitted from **every** `H_n`.

For each `n`, maximality of `H_n` supplies a nonempty set

\[
W_{H_n}(xy)\subseteq N_G(x)\cap N_G(y)
\]

of vertices certifying why `xy` cannot be inserted while preserving triangle-freeness. Since `G` is K4-free, the common neighborhood of the adjacent pair `x,y` is stable, so every such certificate set is stable.

**Recovered status:** `PROVED_IN_PACKET`.  
**Recovered source metadata:** proof=true, Lean=true, falsifier=true.  
Those flags are source metadata, not an independent release-day replay.

## Minimal-Transversal Page Certificate Theorem

Let `D` be an inclusion-minimal triangle transversal of a K4-free graph `G`, and put

\[
H=G-D.
\]

For every edge `xy in D`, minimality implies there is a triangle that would become uncovered if `xy` were removed from the transversal. Equivalently, there is a vertex `z` such that

\[
xz,yz\in H.
\]

All such page vertices `z` lie in

\[
N_G(x)\cap N_G(y),
\]

which is stable because `G` is K4-free. Thus every minimal-transversal edge is the spine of a nonempty stable book whose pages use exactly one transversal edge.

**Recovered status:** `PROVED_IN_PACKET`.  
**Recovered source metadata:** proof=true, Lean=true, falsifier=true.

These lemmas are structural tools around #595. They do not construct a #595 witness and do not close the parent problem.

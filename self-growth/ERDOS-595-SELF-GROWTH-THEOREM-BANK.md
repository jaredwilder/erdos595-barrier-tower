# Erdős #595 — Self-Growth Theorem Bank

Recovered from the 2026-08-04 self-growth packet. The atlas carried these statements twice (cards + packet), so this release uses the **16 unique mathematical statements**, not the duplicated provenance count.

`tc(G)` denotes the least number/cardinal of triangle-free edge layers covering `E(G)`. The flagship Erdős #595 problem remains **NOT CLOSED**.

## D0 — Cover–Partition Equivalence
**Status:** `UNCONDITIONAL_ELEMENTARY`

For every graph `G` and cardinal `lambda`, the following are equivalent:

1. `E(G)` is covered by `lambda` triangle-free subgraphs;
2. `E(G)` is partitioned into `lambda` triangle-free edge sets;
3. there is an edge-coloring `c:E(G)->lambda` with no monochromatic triangle.

## T1 — The `kappa`-Complete Triangle-Cover Ideal
**Status:** `UNCONDITIONAL_ELEMENTARY`

For infinite `kappa`, define

\[
\mathcal I_\kappa(G)=\{F\subseteq E(G):tc((V(G),F))\le\kappa\}.
\]

Then `I_kappa(G)` is downward closed and closed under unions of at most `kappa` members.

## T2 — Null-Edge Deletion Persistence
**Status:** `UNCONDITIONAL_ELEMENTARY`

If `kappa` is infinite, `tc(G)>kappa`, and `F in I_kappa(G)`, then

\[
tc(G-F)>\kappa.
\]

## C2.1 — No Edge-Minimal High-Cover Graph
**Status:** `UNCONDITIONAL_COROLLARY`

If `kappa` is infinite and `tc(G)>kappa`, deleting any single edge, any set of at most `kappa` edges, or more generally any edge set of triangle-cover number at most `kappa`, leaves triangle-cover number greater than `kappa`. Hence no such graph is edge-minimal for `tc>kappa`.

## T3 — Small-Vertex Deletion Persistence
**Status:** `UNCONDITIONAL_ELEMENTARY`

If `tc(G)>kappa` and `S subset V(G)` has `|S|<=kappa`, then

\[
tc(G-S)>\kappa.
\]

## T4 — Component Supremum Formula
**Status:** `UNCONDITIONAL_ELEMENTARY`

If `G` is the disjoint union of connected components `{G_i:i in I}`, then

\[
tc(G)=\sup_i tc(G_i).
\]

## T5 — Small-Separator Escape
**Status:** `UNCONDITIONAL_ELEMENTARY`

If `tc(G)>kappa` and `|S|<=kappa`, some connected component `C` of `G-S` satisfies

\[
tc(C)>\kappa.
\]

## T6 — Ordered Forward-Link Coloring
**Status:** `UNCONDITIONAL_ELEMENTARY`

Fix a well-order `prec` of `V(G)` and define

\[
N_\prec^+(v)=\{w\in N_G(v):v\prec w\}.
\]

If every forward link `G[N_prec^+(v)]` is `kappa`-colorable, then

\[
tc(G)\le\kappa.
\]

## T7 — High-Cover Link Extraction in `K4`-Free Graphs
**Status:** `UNCONDITIONAL_ELEMENTARY`

If `G` is `K4`-free and `tc(G)>kappa`, then for every well-order `prec` some vertex `v` satisfies

\[
\chi(G[N_\prec^+(v)])>\kappa,
\]

and this forward link is triangle-free.

## T8 — Successor-Length Forward-Link Tower
**Status:** `UNCONDITIONAL_TRANSFINITE`

If `kappa` is infinite and `G` is `K4`-free with `tc(G)>kappa`, there is a sequence

\[
\langle(v_\alpha,L_\alpha):\alpha<\kappa^+\rangle
\]

of distinct vertices `v_alpha` and induced triangle-free `L_alpha subset N_G(v_alpha)` satisfying

\[
\chi(L_\alpha)>\kappa.
\]

## T9 — Stable Certification of Omitted Edges
**Status:** `UNCONDITIONAL_ELEMENTARY`

Let `G` be `K4`-free and `H` a maximal spanning triangle-free subgraph. If `xy in E(G)\E(H)`, define

\[
W_H(xy)=N_H(x)\cap N_H(y).
\]

Then `W_H(xy)` is nonempty and stable in `G`.

## T10 — Common Omitted-Edge Stable Book
**Status:** `UNCONDITIONAL_ELEMENTARY`

Let `kappa` be infinite, `G` be `K4`-free, and `tc(G)>kappa`. For every family `{H_i:i in I}` of maximal spanning triangle-free subgraphs with `|I|<=kappa`, there is an edge `xy` omitted by every `H_i`. For each `i`, `W_{H_i}(xy)` is a nonempty stable subset of `N_G(x) cap N_G(y)`.

## T11 — Stable Triangle-Book Sterility
**Status:** `UNCONDITIONAL_ELEMENTARY`

Let `xy` be an edge and `W subset N(x) cap N(y)` a nonempty stable set. If `B(xy,W)` has edge set

\[
\{xy\}\cup\{xw,yw:w\in W\},
\]

then

\[
tc(B(xy,W))=2.
\]

## T12 — Countable Book-Deletion Persistence
**Status:** `UNCONDITIONAL_COROLLARY`

If `G` is `K4`-free with `tc(G)>aleph_0`, and `F` is the union of the edge sets of countably many stable triangle books, then

\[
tc(G-F)>\aleph_0.
\]

## T13 — `omega_1` Disjoint Critical-Cone Packing
**Status:** `UNCONDITIONAL_WITH_STANDARD_COMPACTNESS`

Let `G` be `K4`-free with `tc(G)>aleph_0`, and let `f:omega_1->omega`. Then `G` contains pairwise vertex-disjoint induced subgraphs

\[
K_1\vee Q_\alpha\qquad(\alpha<\omega_1),
\]

where every `Q_alpha` is finite, triangle-free, vertex-critical, and

\[
\chi(Q_\alpha)>f(\alpha).
\]

## C14 — Conditional `omega_1` Cone Packing from Erdős #738
**Status:** `CONDITIONAL_ON_ERDOS_738_FOR_T`

Fix a finite tree `T`. Assume every triangle-free graph of infinite chromatic number contains an induced copy of `T`. Then every `K4`-free graph `G` with `tc(G)>aleph_0` contains `omega_1` pairwise vertex-disjoint induced copies of

\[
K_1\vee T.
\]

## Relationship to the rest of the public #595 estate

Several of these statements also feed the public `erdos738-frontier/X595-CROSS-THEOREM-BANK.md` and the later barrier/refinery program. They are retained here because this is the canonical self-growth layer from which those bridges were built. Duplication of provenance is not counted as new mathematics.

**Court:** structural theorem bank only. No witness to Erdős #595 is constructed and no refutation of the problem is proved.
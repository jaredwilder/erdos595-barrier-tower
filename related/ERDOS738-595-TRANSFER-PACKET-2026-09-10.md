# Erdős #738 ↔ #595 Graph-Transfer Packet

**Author:** Jared Wilder  
**Public release:** 2026-09-10

## Global status

Both parent problems remain open in current public sources as of this release. Erdős #738 is the triangle-free infinite-chromatic induced-tree problem / a close relative of the Gyárfás–Sumner program, and Erdős #595 asks for an infinite K4-free graph not expressible as a countable union of triangle-free graphs.

This packet releases the exact **transfer mathematics** between the two programs. Conditional results remain conditional on the named #738 hypothesis.

The underlying estate contains **197 theorem records** across four domains:

- `erdos-738-encirclement`: 62
- `erdos-738-x`: 41
- `erdos-595-encirclement`: 62
- `erdos-595-self`: 32

Of those, 152 carry the packet-local status `PROVED_IN_PACKET`, with additional unconditional elementary/transfinite/corollary statements and a small explicit conditional layer.

# I. #595 triangle-cover calculus

Let `tc(G)` denote the least cardinal number of triangle-free subgraphs whose union is `G`.

## Union subadditivity

For any family `(G_i)`,

\[
tc\!\left(\bigcup_iG_i\right)\le\sum_i tc(G_i)
\]

in cardinal arithmetic.

Consequently:

- a countable union of countably triangle-coverable graphs is countably triangle-coverable;
- more generally, for every infinite cardinal `κ`, the class `{G:tc(G)<=κ}` is closed under unions of at most `κ` members of the same class;
- if `G=⋃_{i<δ}G_i` and each `tc(G_i)<=κ`, then `tc(G)<=κ·|δ|`.

## Trivial countable-edge stratum

Every graph with at most countably many edges is a countable union of one-edge graphs, hence has

\[
tc(G)\le\aleph_0.
\]

Thus any #595 witness must have uncountably many edges.

## Finite obstruction extraction

If

\[
tc(G)>\aleph_0,
\]

then for every positive integer `k`, `G` contains a finite subgraph `F` with

\[
tc(F)>k.
\]

This is one bridge from the infinitary problem to finite high-cover obstructions.

## Bounded-degree cover bound

If `G` has finite maximum degree `Δ`, then

\[
\boxed{tc(G)\le\lceil\log_2(\Delta+1)\rceil.}
\]

Hence every locally finite graph with exact triangle-cover number `aleph_0` must have unbounded degrees.

## Cardinal chromatic bounds

The packet contains the pair of cardinal implications

\[
tc(G)>\kappa\Longrightarrow\chi(G)>2^\kappa,
\]

and

\[
\chi(G)\le2^\kappa\Longrightarrow tc(G)\le\kappa.
\]

More generally, if `G` is the union of `κ` subgraphs each of chromatic number at most `μ`, then

\[
\chi(G)\le\mu^\kappa.
\]

For a hereditary graph class `C`, writing

\[
\tau_C(G)=\sup\{\chi(F):F\subseteq G,\ F\in C\},
\]

an edge cover of `G` by `κ` members of `C` yields

\[
\chi(G)\le\tau_C(G)^\kappa.
\]

Taking `C` to be the triangle-free graphs gives the chromatic-dispersion obstruction used repeatedly in the #595 program.

## Continuum-gap close lemma

If

\[
\chi(G)=(2^{\aleph_0})^+
\]

and every triangle-free subgraph of `G` has chromatic number at most `2^{\aleph_0}`, then `G` cannot be a countable union of triangle-free subgraphs.

This is a sufficient criterion, not a construction of a K4-free graph satisfying it.

## Uncountable-cofinality constraint

If the least vertex cardinality of a #595 witness exists, it has uncountable cofinality. The same holds for the least edge cardinality.

The reason is closure under countable increasing unions of smaller coverable pieces.

# II. K4-free link structure

## K4-free links are triangle-free

For every vertex `v` in a K4-free graph,

\[
G[N(v)]
\]

is triangle-free. The same holds for every forward neighborhood under a vertex well-order.

## Common-neighbor independence

If `uv` is an edge of a K4-free graph, then

\[
N(u)\cap N(v)
\]

is independent.

## Finite high-cover link extraction

If `G` is finite, K4-free, and

\[
tc(G)>k,
\]

then some vertex `v` has a triangle-free neighborhood with

\[
\chi(G[N(v)])>k.
\]

For any prescribed vertex order, a forward neighborhood can be used instead.

## Ordered link parameter

Define

\[
\lambda_\triangle(G)=\min_{\prec}\sup_{v\in V(G)}\chi(G[N^+_\prec(v)]),
\]

where the minimum runs over well-orders. Then

\[
\boxed{tc(G)\le\lambda_\triangle(G).}
\]

## Erdős #595 Link Theorem

Every K4-free graph `G` with

\[
tc(G)>\aleph_0
\]

has the following property:

> for **every** well-order of `V(G)`, some forward neighborhood is an uncountably chromatic triangle-free induced subgraph.

## Link-cover dispersion

Every #595 witness has uncountable closed-neighborhood edge-cover number, and in particular has no countable vertex cover.

Together with the Link Theorem this yields a localization–dispersion dichotomy:

- very high vertex-chromatic complexity localizes inside a triangle-free link;
- triangle-cover complexity cannot be concentrated in countably many local neighborhoods.

# III. Why a single high-chromatic link is not the whole obstruction

The packet contains an exact warning against a tempting false compression.

For every cardinal `κ` realized as the chromatic number of some triangle-free graph `H`, the cone

\[
G=K_1\vee H
\]

is K4-free, has a vertex whose neighborhood has chromatic number `κ`, yet

\[
tc(G)=2.
\]

So an arbitrarily complicated triangle-free link by itself does **not** create high triangle-cover number.

Likewise, the critical bouquet structures forced conditionally by #738 can themselves remain two-layer coverable. The #595 obstruction must live in the interaction among many such local structures.

# IV. Triangle-hypergraph realizability

Let `Tri(G)` be the 3-uniform hypergraph of triangles of `G`.

## Subhypergraph embedding theorem

A 3-uniform hypergraph `H` embeds as a subhypergraph of `Tri(G)` for some simple graph `G` exactly when its vertices admit an injective endpoint-pair representation

\[
\rho:V(H)\to[X]^2
\]

such that every hyperedge maps to the three edges of a graph triangle. Extra graph triangles are permitted in this subhypergraph version.

## K4-free exact-realization certificate

If a finite 3-uniform hypergraph has an exact endpoint representation of the packet's type and contains no Berge triangle, then the realizing graph is K4-free.

## #595 witness reduction

If an uncountably chromatic 3-uniform hypergraph `H` has no Berge 3-cycle and is **exactly realizable** as `Tri(G)`, then the resulting `G` is a K4-free #595 witness.

A broader equivalence in the archive is explicitly **conditional** on an unresolved exact-realizability theorem for all linear Berge-C3-free 3-uniform hypergraphs. That bridge is not promoted here.

# V. Exact triangle-free graph tools from the #738 program

The #738 theorem bank contains a large collection of elementary-but-useful induced-structure lemmas.

## Neighborhood stability

In every triangle-free graph, each open neighborhood is stable.

## Closed-neighborhood and dominating-set bounds

If `S` is finite and `G[S]` has no isolated vertices, then

\[
\chi(G[N[S]])\le|S|.
\]

If isolated vertices are present, the packet's sharp variant is

\[
\chi(G[N[S]])\le|S|+1.
\]

If `S` is a connected dominating set with `|S|>=2`, then

\[
\chi(G)\le|S|.
\]

A dominating induced path on `n>=2` vertices therefore gives

\[
\chi(G)\le n.
\]

## Chromatic reserve after protected deletion

If `G[S]` has no isolated vertices, then

\[
\chi(G-N[S])\ge\chi(G)-|S|.
\]

Sequential protected deletions give the additive ledger

\[
\chi(G_m)\ge\chi(G)-\sum_i|S_i|.
\]

In an infinite-chromatic triangle-free graph, deleting the closed neighborhood of any finite such `S` leaves infinite chromatic number.

## Critical escape component

If `G` is finite, `k`-vertex-critical and triangle-free, and an induced path `P` has `n<k` vertices, then some component of

\[
G-N[P]
\]

has chromatic number at least `k-n`.

The theorem bank gives the analogous statement for a connected finite induced subgraph `G[S]` of size `<k`.

## No clique cutset

A finite vertex-critical graph has no clique cutset. In particular, every two-vertex cutset of a triangle-free vertex-critical graph is independent.

# VI. Path-contact calculus

Let `P=v_0...v_{n-1}` be an induced path in a triangle-free graph.

## Contact gap

An outside vertex cannot be adjacent to consecutive vertices of `P`; consecutive contact indices differ by at least two.

If the graph is also C4-free, the gap is at least three.

More generally, if the graph has no induced `C_{d+2}`, consecutive contact indices cannot differ by `d`.

## Consecutive contacts create an induced cycle

If `i<j` are consecutive contact indices for an outside vertex `x`, then

\[
G[\{x,v_i,\dots,v_j\}]\cong C_{j-i+2}.
\]

## Fibonacci signature count

In the triangle-free case, the possible contact signatures on an `n`-vertex path are subsets with no consecutive indices, hence there are at most

\[
F_{n+2}
\]

of them.

For gap at least `d`, the signature count obeys

\[
a_d(n)=a_d(n-1)+a_d(n-d)
\]

with the natural initial conditions.

## Stable signature fibers

For a fixed **nonempty** contact signature, all outside vertices realizing that signature form a stable set.

For any fixed path vertex `p`, the entire family of outside vertices whose signature contains `p` is stable.

## Path-contact zone bound

All vertices having at least one neighbor in an `n`-vertex induced path induce a graph of chromatic number at most `n`.

# VII. Mixing, spiders and fans

## First-transition arm

If a vertex `v` is mixed on a connected set `C`, there are adjacent `a,b in C` such that `va` is an edge and `vb` is not. Thus `v-a-b` is induced.

## Two-region mixing forces P5

If `v` is mixed on two anticomplete connected regions, the graph contains an induced `P5`.

## Mixed-region subdivided star

If `v` is mixed on `q` pairwise anticomplete connected regions, the graph contains an induced once-subdivided `K_{1,q}` centered at `v`.

The maximum possible such `q` equals the packet's one-step mixing number `μ_1(v)`.

## Reach-profile spider extraction

If each region contains a vertex at prescribed distance `r_i` from its contact boundary with `N(v)`, one obtains an induced spider with arm lengths `r_i+1`.

Thus excluding a prescribed induced spider bounds the number and reach of pairwise anticomplete regions on which one vertex can be mixed.

## Induced K_{2,m}

If nonadjacent vertices `u,v` have at least `m` common neighbors in a triangle-free graph, those vertices induce a `K_{2,m}`.

This turns common-neighbor crowding into a concrete induced obstruction.

# VIII. Type-uniform rooted-tree mathematics

The #738 encirclement packet studies complete ordered rooted trees embedded in a triangle-free graph with path-induced, level-stable and type-uniform conditions.

For incomparable vertices, adjacency is recorded by a tensor `A_c(a,b)` indexed by their two depths and join depth.

Proved packet constraints include:

- diagonal vanishing `A_c(a,a)=0`;
- parent exclusion in either coordinate;
- for fixed `c`, the support of `A_c` is an independent set in a Cartesian depth grid;
- the number of active ordered types in a slice of height `n` is at most
  \[
  \lfloor n^2/2\rfloor;
  \]
- a parity-defect host attains these active-type bounds exactly;
- embeddings with the same ordered target-pair type profile have the same extra-edge defect graph.

The parity-defect construction is itself triangle-free and supplies sharpness examples for these tensor bounds.

# IX. Exact #738 → #595 conditional transfers

These theorems are conditional and remain labeled that way.

Fix a finite tree `T` and suppose the triangle-free Gyárfás–Sumner / Erdős #738 statement holds for `T`: every triangle-free graph with sufficiently large chromatic number contains an induced `T`.

Then:

## Cone universality

Every #595 witness contains an induced

\[
K_1\vee T.
\]

## Tree-cone transfer bound

If every triangle-free induced-`T`-free graph is `c(T)`-colorable, then every K4-free induced-`(K_1∨T)`-free graph satisfies

\[
tc(G)\le c(T).
\]

## Transversal-absorbed tree theorem

If `D` is a triangle transversal and

\[
\chi(G-D)>c(T),
\]

then `G-D` contains an induced `T`, and every ambient chord of that copy belongs to `D`.

This is the packet's **Exact Tree-Absorption Dictionary**: induced copies in the cleaned graph correspond to tree edges avoiding the defect set while every non-tree ambient edge is absorbed into it.

## Tree-rich layer products

If

\[
E(G)=\bigcup_{i<m}E(H_i)
\]

with every `H_i` triangle-free and induced-`T`-free, then

\[
\chi(G)\le c(T)^m.
\]

The same definition yields a cardinal induced-tree-free layer-cover parameter with the analogous product bound.

## Forced-tree corollaries

If `χ(G)>c(T)^m`, then every `m`-layer triangle-free cover contains a layer with an induced `T`.

If a countable triangle-free cover exists and

\[
\chi(G)>c(T)^{\aleph_0},
\]

then every such cover has a layer containing `T`.

## ω1 disjoint cone packing

Under the same fixed-tree #738 hypothesis, every #595 witness contains

\[
\omega_1
\]

pairwise vertex-disjoint induced copies of `K_1∨T`.

## Full-#738 bouquet consequence

If #738 holds for every finite tree, then every #595 witness contains an induced cone over a countable forest having one component isomorphic to every finite tree.

A stronger sequence version in the estate assumes #738 separately for a prescribed tree sequence and gives the corresponding forest bouquet.

# X. A conditional countable core

Using finite Folkman input as an external hypothesis, the packet constructs a connected, locally finite, one-ended, countable K4-free graph `H` with

\[
tc(H)=\aleph_0.
\]

This does not solve #595 because `aleph_0` is still countable; it isolates a highly structured exact-countable-cover core.

# XI. What remains genuinely open

The transfer program does **not** supply:

- a K4-free graph with `tc>aleph_0`;
- a proof of #738 for arbitrary finite trees;
- the broad exact-realizability theorem for the hypergraph reduction;
- a theorem turning one uncountably chromatic link into globally uncountable triangle-cover number — cones show that implication is false in that naive form.

The durable outcome is a sharper map of what a #595 witness must look like and exactly how progress on #738 would propagate into it.

## Current-status note

The full Gyárfás–Sumner conjecture remains unproved in current public literature; #738 is likewise still publicly listed as open. #595 is also still marked research-open in current formal/public problem sources. This packet therefore keeps all parent-problem language open. 

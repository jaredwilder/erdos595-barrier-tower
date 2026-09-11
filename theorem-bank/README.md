# Erdős #595 — recovered triangle-cover theorem bank

This directory promotes a recovered 2026-08-04 theorem packet into the main Erdős #595 repository.

The source contains **65 theorem cards** (`T01`–`T66`, with no `T57`):

- 60 proved in the packet;
- 1 proved using standard compactness;
- 1 proved from a finite Folkman input;
- 1 source-derived statement requiring prior-art recheck;
- 1 conditional reduction;
- 1 explicitly refuted route.

The exact source ledger remains in the public provenance archive at:

`jaredwilder/unpublished-math-papers/erdos595-triangle-cover/THEOREM-LEDGER.md`

This page surfaces the mathematical structure so that the ledger is no longer discoverable only by knowing the archive path.

## Cover and duality structure

The packet develops several exact formulations of the triangle-cover number `tc(G)`:

- cover-to-partition refinement;
- `tc(G)` as the chromatic number of the triangle hypergraph `Tri(G)`;
- edge-coloring formulation;
- blocker/vertex-cover centeredness duality;
- triangle-transversal centeredness equivalence;
- finite / countable / uncountable centeredness trichotomy.

For the least number `bc(G)` of bipartite subgraphs covering `E(G)`, it proves the exact cardinal relation:

> `bc(G)` is the least cardinal `kappa` such that `chi(G) <= 2^kappa`.

In the finite case this becomes `bc(G)=ceil(log_2 chi(G))` for graphs with an edge, and `tc(G)<=bc(G)`.

## Cardinal barriers and witness structure

The packet proves:

- `tc(G)>kappa => chi(G)>2^kappa`;
- in particular, any non-countably-coverable graph has more than continuum-many vertices and edges;
- minimal witness vertex/edge cardinalities have cofinality greater than the cover cardinal, hence uncountable cofinality in the #595 setting;
- a witness with `tc(G)>aleph_0` contains finite subgraphs with arbitrarily large finite triangle-cover number;
- it therefore contains a countable subgraph `H` with `tc(H)=aleph_0`, preserving `K4`-freeness when present;
- using standard finite Folkman inputs, one can construct a connected, locally finite, one-ended, countable `K4`-free graph with exact triangle-cover number `aleph_0`;
- any locally finite exact-`aleph_0` core has unbounded degree.

These results complement the formal continuum barrier proved elsewhere in this repository.

## Chromatic-dispersion machinery

Let

`tau(G)=sup{chi(H): H subset G and H triangle-free}`.

The packet establishes product-coloring bounds including

`tc(G)<=kappa => chi(G)<=tau(G)^kappa`,

and hence the obstruction

`chi(G)>tau(G)^kappa => tc(G)>kappa`.

It also records fixed-point and continuum-gap criteria, finite-layer analogues, and extensions from triangle-free graphs to arbitrary hereditary graph classes.

## Triangle-hypergraph structure

For `Tri(G)`, whose vertices are the edges of `G` and whose hyperedges are graph triangles, the packet proves:

- `Tri(G)` is a linear 3-uniform hypergraph;
- `G` is `K4`-free iff `Tri(G)` contains no Berge 3-cycle;
- exact endpoint-representation criteria for which 3-uniform hypergraphs arise as `Tri(G)`;
- an embedding variant allowing extra graph triangles;
- finite exact realizability is in NP;
- a `K4`-free realization certificate under the endpoint representation plus Berge-`C3` exclusion;
- recovery from a line graph together with its Krausz star-clique partition;
- witness reductions from uncountably chromatic realizable or embedded hypergraphs.

A broader realizability bridge remains conditional.

## Preserved negative result

The proposed route asserting a fixed bound on the number of triangles containing one edge in a `K4`-free graph is false. Book graphs provide arbitrarily large triangle multiplicity while remaining `K4`-free. The failed route is retained explicitly rather than disappearing from the research history.

## Evidence status

The theorem-card statuses above are the source statuses from the recovered packet. They are not automatically upgraded to Lean verification or historical novelty claims. The strongest formal results in this repository are separately identified in the Lean barrier package.

Author: Jared Wilder. Source date: 2026-08-04. Public subject-repo promotion: 2026-09-11.

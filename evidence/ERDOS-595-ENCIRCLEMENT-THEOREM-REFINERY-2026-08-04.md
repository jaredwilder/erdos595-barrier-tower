# Erdős #595 Encirclement Theorem Refinery
## 66 theorem cards, 18 finite/computational targets, and 12 forced-close programs

**Date:** 2026-08-04  
**Campaign:** `mec-erdos595-theorem-refinery`  
**Owner:** Jared Wilder / Oracle research estate  
**Mode:** Maximum theorem mining under Search/Court separation  
**Novelty status:** **UNRUN** — every historical novelty label must be supplied by the local novelty checker  
**Lean status:** **UNRUN** — Lean target names below are missions, not compilation receipts

---

## 0. Claim boundary

The source-bound flagship used in this artifact is:

\[
\exists G\;\bigl(K_4\nsubseteq G\ \land\ E(G)\text{ is not the union of countably many triangle-free edge sets}\bigr).
\]

Equivalently, with `tc(G)` denoting the least number of triangle-free edge layers covering `E(G)`, the target is a K₄-free graph with `tc(G)>ℵ₀`.

This file does **not** claim the flagship is solved. It converts the encirclement campaign into exact theorem statements, proof routes, falsifiers, Lean missions, novelty queries, finite searches, and complete proof programs. The constitution requires that attractive statements remain proposals until the Court verifies them.

### Source estate used

- `MATH-ENCIRCLEMENT-ENGINE-BUILD-AND-PROOF-PLAN-2026-08-03.md` — target locks, Search/Court separation, forced-close compiler, authority ladder, novelty binding.
- `ENCIRCLEMENT-RSI-DISCOVERY-ENGINE-PERMANENT-BLUEPRINT-2026-08-04.md` — compression-or-destruction, theorem-mining operators, RSI receipts, Lean/novelty routing.
- `Erdos595.txt` — retained only as a hostile/failure corpus; its closure, independence, shift-graph, and local-density claims are quarantined below.
- The full Erdős #595 encirclement rounds in the session — semantic repair, triangle-hypergraph language, cardinal barrier, dispersion route, compactness route, and representation optimization.

---

## 1. Notation

- `tc(G)`: least cardinality of a cover of `E(G)` by triangle-free subgraphs.
- `bc(G)`: least cardinality of a cover of `E(G)` by bipartite subgraphs.
- `Tri(G)`: 3-uniform hypergraph whose vertices are `E(G)` and whose hyperedges are the three edge sets of graph triangles.
- `Tr(G)`: family of triangle transversals, i.e. edge sets meeting every triangle.
- `τ(G)`: supremum of chromatic numbers of triangle-free subgraphs of `G`.
- A family of sets is `κ-centered` here when every subfamily of cardinality at most `κ` has nonempty intersection.
- `Berge C₃`: three hyperedges whose pairwise intersections are three distinct vertices.

---

## 2. Highest-value discoveries emitted by this refinery

1. **Blocker-centeredness duality:** `tc(G)>κ` iff every `≤κ`-sized family of triangle transversals has nonempty intersection (`T04–T06`).
2. **Exact continuum barrier:** every #595 witness must have chromatic, vertex, and edge cardinality strictly above the continuum (`T07–T12`).
3. **Cofinality obstruction:** the least cardinality of a `tc>κ` graph has cofinality above `κ` (`T23–T25`).
4. **Countable exact-ω core:** every uncountable-cover witness contains a countable K₄-free subgraph with `tc=ℵ₀` (`T27–T29`).
5. **Chromatic-dispersion close:** `χ(G)>τ(G)^κ` forces `tc(G)>κ`; the fixed-point form yields a certified finish once the construction exists (`T38–T43`).
6. **K₄ as a Berge triangle:** `G` is K₄-free iff `Tri(G)` has no Berge `C₃` (`T52–T53`).
7. **Exact endpoint-realizability language:** graph-triangle hypergraphs admit a precise pair-representation characterization and finite NP certificate (`T58–T61`).
8. **Concrete zero-to-one construction:** known finite Folkman obstructions assemble into a connected locally finite one-ended countable K₄-free graph with exact cover number `ℵ₀` (`T33`).

---

## 3. Theorem bank

Statuses:

- `PROVED_IN_PACKET`: elementary proof is supplied here.
- `PROVED_USING_STANDARD_COMPACTNESS`: exact proof route is standard but should be source-bound/formalized.
- `PROVED_FROM_FINITE_FOLKMAN_INPUT`: deduction is proved conditional on the known finite input.
- `SOURCE_DERIVED_PRIOR_ART_RECHECK_REQUIRED`: session source anchor; local binder must verify exact publication statement.
- `CONDITIONAL_REDUCTION`: implication proved, load-bearing hypothesis still open.
- `REFUTED_ROUTE`: negative result permanently kills a campaign mechanism.

### Package A — Exact equivalences and cardinal barriers

#### T01 — Cover-to-partition refinement

- **Statement:** For every graph G and cardinal κ, if E(G) is the union of κ triangle-free edge sets, then E(G) can be partitioned into κ triangle-free edge sets.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Well-order the κ layers and assign each edge to the least layer containing it. Each refined class is a subset of an original triangle-free class.
- **Falsifier:** A cover for which every attempted least-layer refinement creates a triangle inside a refined class.
- **Lean mission:** `triangleFreeCover_refines_to_partition`
- **Novelty query:** `"triangle-free edge cover" partition refinement graph`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `55/100`
- **Claim hash:** `601eb21d22653b22d7d9e6014de335e9eec4f857138d9243ebc987ffd56641cd`

#### T02 — Triangle-hypergraph chromatic equivalence

- **Statement:** Let Tri(G) be the 3-uniform hypergraph with vertex set E(G) and one hyperedge for each triangle of G. Then the triangle-cover number tc(G) equals the vertex chromatic number χ(Tri(G)), where a hypergraph coloring is proper when no hyperedge is monochromatic.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** A triangle-free edge color class is exactly an independent set of Tri(G); apply T01 to pass between covers and colorings.
- **Falsifier:** A graph and a coloring counted by one side but not the other.
- **Lean mission:** `triangleCoverNumber_eq_triangleHypergraphChromatic`
- **Novelty query:** `"triangle hypergraph" chromatic number edge partition triangle-free`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `95/100`
- **Claim hash:** `9acc522d4cfccb5069cfec380971885b36f3bc8028ccbcc70bb3f4f0ac197c9b`

#### T03 — Edge-coloring formulation

- **Statement:** For every graph G and cardinal κ, tc(G) ≤ κ if and only if there exists c : E(G) → κ such that the three edges of every triangle are not all assigned the same value.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Unpack T02: color classes are triangle-free exactly when every triangle is nonmonochromatic.
- **Falsifier:** A coloring satisfying one direction but whose color classes violate the other.
- **Lean mission:** `triangleCover_iff_nonmonochromatic_edgeColoring`
- **Novelty query:** `"edge coloring" every triangle nonmonochromatic countable colors`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `100/100`
- **Claim hash:** `e75ece3386ceb0ad177be97300d28f7937cad1fa5e513333c036ca7ad7bf78f8`

#### T04 — General blocker-centeredness duality

- **Statement:** For every hypergraph H on vertex set X and every cardinal κ, χ(H) ≤ κ if and only if there exist κ vertex covers D_i of H with ⋂_{i<κ} D_i = ∅. Consequently, χ(H) is the least cardinality of a subfamily of vertex covers having empty intersection.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Given independent color classes A_i, take D_i=X\A_i. Conversely, complements of vertex covers are independent and an empty intersection means their complements cover X; refine by T01's set-theoretic argument.
- **Falsifier:** A hypergraph where complements fail to exchange independent sets and vertex covers.
- **Lean mission:** `hypergraphChromatic_eq_min_emptyIntersection_vertexCovers`
- **Novelty query:** `"hypergraph chromatic number" "vertex covers" empty intersection duality`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `97/100`
- **Claim hash:** `a05db37a42b25a05a499f904c4fdc935638aef5a11d593f80708325254ed4ce7`

#### T05 — Triangle-transversal centeredness equivalence

- **Statement:** Let Tr(G) be the family of edge sets meeting every triangle of G. For every cardinal κ, tc(G) > κ if and only if every subfamily of Tr(G) of cardinality at most κ has nonempty intersection.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Apply T04 to Tri(G). Vertex covers of Tri(G) are exactly triangle transversals of G.
- **Falsifier:** A family of κ triangle transversals with empty intersection while tc(G)>κ, or the converse.
- **Lean mission:** `triangleCover_gt_iff_transversals_centered`
- **Novelty query:** `"triangle transversals" countable intersection property edge coloring`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `100/100`
- **Claim hash:** `9a368293bb3116740cabae9b97e0d6262b39cf08194f26f7eea58fe420ad5647`

#### T06 — Centeredness trichotomy

- **Statement:** For a graph G with at least one triangle: (i) tc(G)=n<ω exactly when n is the least size of a triangle-transversal family with empty intersection; (ii) tc(G)=ℵ₀ exactly when Tr(G) has the finite-intersection property but has a countable subfamily with empty intersection; (iii) tc(G)>ℵ₀ exactly when Tr(G) is countably centered.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Specialize T05 to finite n and κ=ℵ₀, using the definition of least cover cardinal.
- **Falsifier:** A graph whose tc-value and transversal intersection behavior fall in different cases.
- **Lean mission:** `triangleCover_centeredness_trichotomy`
- **Novelty query:** `"triangle transversal family" finite intersection property countably centered`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `93/100`
- **Claim hash:** `1e4a24e8e7d5abf625a5c80513af1186c19a00b183b055aa7716ee728826e35b`

#### T07 — Exact bipartite-cover cardinal theorem

- **Statement:** Let bc(G) be the least cardinal κ such that E(G) is covered by κ bipartite subgraphs. Then bc(G) is the least κ satisfying χ(G) ≤ 2^κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** If χ(G)≤2^κ, code vertex colors by binary κ-sequences and use one bipartite layer per coordinate. Conversely, concatenate chosen bipartitions of κ covering layers into a proper 2^κ-valued vertex coloring.
- **Falsifier:** A graph violating either coding direction.
- **Lean mission:** `bipartiteCoverNumber_eq_cardinalLog_chromatic`
- **Novelty query:** `"minimum number bipartite subgraphs cover edges" chromatic logarithm`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `96/100`
- **Claim hash:** `a1313406060b90c81b79aa49c47d36d1f5ca48ba8bfd3db36dc31b7db9e309fe`

#### T08 — Finite logarithmic bipartite cover

- **Statement:** For every finite graph G with at least one edge, bc(G)=⌈log₂ χ(G)⌉.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Finite specialization of T07.
- **Falsifier:** A finite graph whose minimum bipartite edge-cover count differs from the ceiling logarithm of χ(G).
- **Lean mission:** `finite_bipartiteCover_eq_ceillog2_chromatic`
- **Novelty query:** `"bipartite subgraph cover" ceil log2 chromatic number`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `76/100`
- **Claim hash:** `0f0d495a82856237111ccba1d196e396b99d4bf78a3e8ce041453fbe6dbb7d31`

#### T09 — Triangle cover bounded by bipartite cover

- **Statement:** For every graph G, tc(G) ≤ bc(G).
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Every bipartite graph is triangle-free.
- **Falsifier:** A bipartite covering whose layers are not triangle-free.
- **Lean mission:** `triangleCover_le_bipartiteCover`
- **Novelty query:** `"triangle-free cover number" bipartite cover number inequality`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `66/100`
- **Claim hash:** `953673f711a46099d0450beafd6a3d07164f4a37996717357e393f33839110e8`

#### T10 — Cardinal chromatic upper bound

- **Statement:** For every graph G and cardinal κ, χ(G) ≤ 2^κ implies tc(G) ≤ κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Combine T07 and T09.
- **Falsifier:** A graph with χ(G)≤2^κ but no κ-layer triangle-free cover.
- **Lean mission:** `triangleCover_le_of_chromatic_le_two_pow`
- **Novelty query:** `"chromatic number" "countable union of triangle-free graphs" continuum`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `95/100`
- **Claim hash:** `268c7cd293ad51f376ba567bc3d068735e6e22cfbc3d3b2d7f1bd21e03da2b7f`

#### T11 — Cardinal chromatic obstruction

- **Statement:** For every graph G and cardinal κ, tc(G)>κ implies χ(G)>2^κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Contrapositive of T10.
- **Falsifier:** A graph with tc(G)>κ and χ(G)≤2^κ.
- **Lean mission:** `chromatic_gt_two_pow_of_triangleCover_gt`
- **Novelty query:** `"triangle-free decomposition number" chromatic number cardinal lower bound`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `97/100`
- **Claim hash:** `8d1956bfee8c6085ebb7b11293b7d66fcd6bc15c6588dccbb91f0c1a2198268f`

#### T12 — Continuum barrier for Erdős #595

- **Statement:** Any graph G that is not a union of countably many triangle-free subgraphs satisfies χ(G)>2^{ℵ₀}; in particular |V(G)|>2^{ℵ₀} and |E(G)|>2^{ℵ₀}.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Set κ=ℵ₀ in T11. Chromatic number is bounded by |V(G)|, and a graph with chromatic number above the continuum cannot have at most continuum many edges after removing isolated vertices.
- **Falsifier:** A nondecomposable graph of chromatic, vertex, or edge cardinal at most the continuum.
- **Lean mission:** `erdos595_witness_above_continuum`
- **Novelty query:** `"Erdos problem 595" continuum chromatic number lower bound`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `100/100`
- **Claim hash:** `fe1ccc2b4646c44658fcdc742fa31af036c0979bd90f254f6a4549b6efe87bb1`

#### T13 — Countable-edge trivial cover

- **Statement:** Every graph with at most countably many edges is a union of countably many one-edge, hence triangle-free, subgraphs.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Enumerate the edges and place one edge in each layer.
- **Falsifier:** A countable edge set that cannot be enumerated into singleton layers.
- **Lean mission:** `countable_edges_triangleCover_le_aleph0`
- **Novelty query:** `"countable graph" edge partition singleton triangle-free`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `70/100`
- **Claim hash:** `6bb8293a7e6f1ebb4951b5a77f2fc2b24d8fa7ed8c3d82b6431d804ba7294553`

#### T14 — Subgraph monotonicity

- **Statement:** If H is a subgraph of G, then tc(H)≤tc(G).
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Restrict any triangle-free cover or nonmonochromatic edge coloring of G to H.
- **Falsifier:** A subgraph requiring strictly more layers than every cover of its supergraph.
- **Lean mission:** `triangleCover_mono_subgraph`
- **Novelty query:** `"triangle-free edge cover number" monotone subgraph`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `58/100`
- **Claim hash:** `671e57b080beab8a6e3e4d4386dc159aee959806606321162807c8d078979971`

#### T15 — Homomorphism pullback monotonicity

- **Statement:** If there is a graph homomorphism f:G→H between simple graphs, then tc(G)≤tc(H).
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Pull back an edge coloring of H along f. Every triangle of G maps injectively to a triangle of H because loops are forbidden and its vertices are pairwise adjacent.
- **Falsifier:** A simple-graph homomorphism mapping a triangle noninjectively or creating a monochromatic preimage from a proper target coloring.
- **Lean mission:** `triangleCover_le_of_hom`
- **Novelty query:** `"graph homomorphism" triangle-free edge cover pullback`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `79/100`
- **Claim hash:** `2b59ced467d1a6e17fb0a8b8674c6ea39442328f0722ca5241e8e164bb1d2a64`

#### T16 — Independent blow-up invariance

- **Statement:** If B is obtained from a graph G by replacing every vertex with a nonempty independent set and every edge with the corresponding complete bipartite pair, then tc(B)=tc(G).
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** The collapse map B→G is a homomorphism, giving tc(B)≤tc(G) by T15. Choosing one representative in each blow-up class embeds G into B, giving the reverse inequality by T14.
- **Falsifier:** A nonempty independent blow-up changing tc.
- **Lean mission:** `triangleCover_independentBlowup_eq`
- **Novelty query:** `"blow-up graph" triangle-free edge coloring invariant`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `86/100`
- **Claim hash:** `1b8a84b9b8ccf0bfad1d1ae22aaae0f4af842fb867487412891ff7748e892330`

#### T17 — Disjoint-union formula

- **Statement:** For every family of graphs (G_i)_{i∈I}, tc(⊔_{i∈I}G_i)=sup_{i∈I} tc(G_i).
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Restriction gives the lower bound. Reuse one common palette of size the supremum across all components for the upper bound.
- **Falsifier:** A disjoint union needing more colors than the supremum of its components.
- **Lean mission:** `triangleCover_iSup_disjointUnion`
- **Novelty query:** `"disjoint union" triangle cover number supremum`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `72/100`
- **Claim hash:** `98d4f28d66409eed8858b8e495f9432d60e7fc879b4444d3bbe8d8b00e393f4f`

#### T18 — Clique–Ramsey identity

- **Statement:** For every integer n≥3, tc(K_n) is the least positive integer k such that n<R_k(3), where R_k(3) is the diagonal k-color Ramsey number for triangles.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** A k-layer triangle-free partition of K_n is exactly a k-edge-coloring with no monochromatic triangle.
- **Falsifier:** A value of n,k violating the defining Ramsey equivalence.
- **Lean mission:** `triangleCover_completeGraph_eq_multicolorRamseyThreshold`
- **Novelty query:** `"K_n" minimum colors no monochromatic triangle R_k(3)`
- **Prior-art risk:** `LOW`
- **Structural leverage:** `61/100`
- **Claim hash:** `88681650a43440a77f12202bdcc2f376838ac41eaf28d5c30a3de4fd391476eb`

### Package B — Closure, compactness, cofinality, and countable cores

#### T19 — Union subadditivity

- **Statement:** For any family of subgraphs (G_i)_{i∈I} with G=⋃_{i∈I}G_i, tc(G)≤Σ_{i∈I}tc(G_i) in cardinal arithmetic.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Take all triangle-free layers from all covers of the G_i.
- **Falsifier:** A union whose inherited layer family fails to cover an edge or contains a triangle.
- **Lean mission:** `triangleCover_union_le_sum`
- **Novelty query:** `"triangle cover number" subadditive union graphs`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `80/100`
- **Claim hash:** `f50a7f94f1a42c52ee669486c953b1be8b204629f966e97031ffdbaaa2b2eed0`

#### T20 — κ-union closure

- **Statement:** For every infinite cardinal κ, the class {G:tc(G)≤κ} is closed under unions of at most κ subgraphs from the same class.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Apply T19 and κ·κ=κ.
- **Falsifier:** A ≤κ-sized union of tc≤κ graphs with tc>κ.
- **Lean mission:** `triangleCoverClass_closed_iUnion`
- **Novelty query:** `"countable union of countably triangle-decomposable graphs" closure`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `89/100`
- **Claim hash:** `297473db9b4c28ed93c32f382b4ae2a69559954ddaf40df4ce565acbc46bc5b4`

#### T21 — Countable-union closure

- **Statement:** A countable union of graphs that are each countable unions of triangle-free subgraphs is itself a countable union of triangle-free subgraphs.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Specialize T20 to κ=ℵ₀ and flatten the double sequence of layers.
- **Falsifier:** A doubly countable family that cannot be paired into one countable family.
- **Lean mission:** `countablyTriangleCoverable_closed_countableUnion`
- **Novelty query:** `"countable union" "countable union of triangle-free graphs" flatten`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `91/100`
- **Claim hash:** `a53f9e59d5cfc2847fdb1303a21ca7b81fd3c77e8b723171d7be3e8c80365d7c`

#### T22 — Chain cover bound

- **Statement:** If G=⋃_{i<δ}G_i and tc(G_i)≤κ for every i, then tc(G)≤κ·|δ|.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Direct instance of T19.
- **Falsifier:** A chain union exceeding the product bound.
- **Lean mission:** `triangleCover_chain_le_mul`
- **Novelty query:** `"increasing union graphs" triangle cover cardinal bound`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `72/100`
- **Claim hash:** `2e8026d104f9254b2ede57bb56a509dac5809bbdd2df8b995fb785849a4f43ed`

#### T23 — Minimal edge-cardinality cofinality theorem

- **Statement:** Fix an infinite cardinal κ. If λ is the least edge cardinality of a graph G with tc(G)>κ, then cf(λ)>κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** If cf(λ)≤κ, express E(G) as an increasing union of ≤κ sets of size <λ. The corresponding spanning subgraphs each have tc≤κ by minimality; T20 then gives tc(G)≤κ.
- **Falsifier:** A least λ with cf(λ)≤κ and a valid counterexample to the chain argument.
- **Lean mission:** `minimal_edgeCard_triangleCover_gt_cofinality`
- **Novelty query:** `"minimal cardinal counterexample" cover number cofinality graph`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `92/100`
- **Claim hash:** `bd8e628cf9e6a9a694ef57cc551030c08d7d968b4c02fe4c31f623abb65a6512`

#### T24 — Minimal vertex-cardinality cofinality theorem

- **Statement:** Fix an infinite cardinal κ. If λ is the least vertex cardinality of a graph G with tc(G)>κ, then cf(λ)>κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** If cf(λ)≤κ, choose an increasing cofinal chain of vertex subsets of size <λ. Their induced subgraphs cover every edge, each has tc≤κ by minimality, and T20 yields a contradiction.
- **Falsifier:** A least λ of small cofinality for which the induced-chain union fails.
- **Lean mission:** `minimal_vertexCard_triangleCover_gt_cofinality`
- **Novelty query:** `"minimal vertex cardinal" triangle-free decomposition cofinality`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `96/100`
- **Claim hash:** `1695886edd7e6f7f13f648ebd5e493db8fb8b2d4be199934e33620345554183b`

#### T25 — Uncountable-cofinality witness constraint

- **Statement:** The least vertex cardinality and the least edge cardinality of an Erdős #595 witness, if either minimum is taken over all witnesses, must each have uncountable cofinality.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Apply T23 and T24 with κ=ℵ₀.
- **Falsifier:** A minimal witness cardinal of countable cofinality.
- **Lean mission:** `erdos595_minimalCard_cofinality_gt_omega`
- **Novelty query:** `"Erdos 595" minimal counterexample cofinality`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `93/100`
- **Claim hash:** `0a9e891a3dd930ebd8a80ecc38560473195b28b4826a83ba87e6a9b817c97586`

#### T26 — Fixed-finite compactness

- **Statement:** For each fixed positive integer k, tc(G)≤k if and only if tc(F)≤k for every finite subgraph F of G.
- **Status:** `PROVED_USING_STANDARD_COMPACTNESS`
- **Proof route:** Encode a k-color for every edge and one finite nonmonochromatic clause per triangle. Every finite set of clauses lies in a finite subgraph; apply propositional compactness. The reverse direction is monotonicity.
- **Falsifier:** A graph all of whose finite subgraphs are k-coverable but which is not k-coverable.
- **Lean mission:** `triangleCover_le_nat_iff_all_finite_subgraphs`
- **Novelty query:** `"de Bruijn Erdos compactness" hypergraph coloring triangles finite subgraphs`
- **Prior-art risk:** `LOW`
- **Structural leverage:** `98/100`
- **Claim hash:** `e17f0c5aa3ebee836b060643ae66317df00d5a3eb3594562985794b15c115574`

#### T27 — Finite obstruction extraction

- **Statement:** If tc(G)>ℵ₀, then for every positive integer k, G contains a finite subgraph F with tc(F)>k.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** If some k bounded all finite subgraphs, T26 would imply tc(G)≤k.
- **Falsifier:** A graph with tc>ℵ₀ but a uniform finite bound on all finite subgraphs.
- **Lean mission:** `triangleCover_gt_aleph0_has_finite_obstructions`
- **Novelty query:** `"uncountable hypergraph chromatic number" finite subhypergraphs unbounded chromatic`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `94/100`
- **Claim hash:** `11550d6579719fdea984894c4e3078896967e77d48483d78ec58b0523091c12b`

#### T28 — Countable exact-ℵ₀ core extraction

- **Statement:** If tc(G)>ℵ₀, then G contains a countable subgraph H with tc(H)=ℵ₀. If G is K₄-free, H may be chosen K₄-free.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** For each k choose finite F_k⊆G with tc(F_k)>k by T27 and let H=⋃_kF_k. Then tc(H)>k for every k, while H has countably many edges and so tc(H)≤ℵ₀ by T13.
- **Falsifier:** A graph with tc>ℵ₀ from which no countable exact-ℵ₀ subgraph can be assembled.
- **Lean mission:** `uncountable_triangleCover_contains_countable_exact_omega_core`
- **Novelty query:** `"countable subgraph" unbounded finite triangle cover number`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `99/100`
- **Claim hash:** `cc97f0fa8b0230b76bc1f8754f11ff48aa0027566f0c89a31c30d422d1077f9a`

#### T29 — Countable exact-ℵ₀ criterion

- **Statement:** For a countable-edge graph H, tc(H)=ℵ₀ if and only if the values tc(F) over finite subgraphs F⊆H are unbounded in the positive integers.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** The forward direction uses T26: a finite bound would globalize. The reverse direction rules out every finite tc-value, while T13 supplies the ℵ₀ upper bound.
- **Falsifier:** "A countable graph with exact ℵ₀ cover number but bounded finite obstructions, or unbounded finite obstructions but finite cover number."
- **Lean mission:** `countable_triangleCover_eq_omega_iff_finite_unbounded`
- **Novelty query:** `"countable hypergraph chromatic number omega" finite subgraph chromatic unbounded`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `96/100`
- **Claim hash:** `48a6863f552a7905847c3c82a87cf6a273101a7e08f1bc4b4bca2cd45269ec8e`

#### T30 — Countable finite-stage sterility

- **Statement:** No graph obtained as a countable union of finite subgraphs can be an Erdős #595 witness.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Such a graph has countably many edges, so T13 applies. Equivalently, each finite stage is countably coverable and T21 closes the union.
- **Falsifier:** A countable finite-stage union with uncountably many edges.
- **Lean mission:** `countable_union_finite_not_erdos595_witness`
- **Novelty query:** `"direct limit finite graphs" countable triangle-free decomposition`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `88/100`
- **Claim hash:** `a3f626ab1a5eb40140212d1b3366ee3a571a829ed602b74ea0fd31025ec92542`

#### T31 — Triangle-inert bridge invariance

- **Statement:** If G' is obtained from G by adding edges that lie in no triangle of G', then tc(G')=max(tc(G),1) (and equals tc(G) whenever G has an edge).
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Monotonicity gives tc(G)≤tc(G'). Put every new triangle-inert edge into any existing triangle-free layer; no triangle can be created using it.
- **Falsifier:** A newly added edge lying in no triangle yet forcing an extra layer.
- **Lean mission:** `triangleCover_invariant_add_triangleInertEdges`
- **Novelty query:** `"adding bridges" triangle-free edge cover number invariant`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `79/100`
- **Claim hash:** `40c5a9e0aac7d58a7a6d2d165c6aff458aa2f5ffd591de729c163988cc0a181a`

#### T32 — Vertex-sum formula

- **Statement:** If a graph G is formed by gluing a family of graphs along vertices only, with no edge shared between distinct pieces and no edge joining their nonshared vertices, then tc(G)=sup_i tc(G_i).
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Every triangle lies entirely in one piece. Reuse a common palette across pieces; restriction gives the lower bound.
- **Falsifier:** A triangle using edges from two vertex-glued pieces.
- **Lean mission:** `triangleCover_vertexSum_eq_iSup`
- **Novelty query:** `"1-sum graph" triangle cover number`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `75/100`
- **Claim hash:** `137b8be2a6b7f7cd78085ece479ee11b86a88b17ea410dc2eb198824b1526424`

#### T33 — Connected locally finite one-ended exact-ℵ₀ core

- **Statement:** Assume that for every k there exists a finite K₄-free graph F_k with tc(F_k)>k. Then there exists a connected, locally finite, one-ended, countable K₄-free graph H with tc(H)=ℵ₀.
- **Status:** `PROVED_FROM_FINITE_FOLKMAN_INPUT`
- **Proof route:** Choose connected components retaining tc(F_k)>k, arrange them along a ray, and join consecutive blocks by bridges. T31 preserves the supremum, local finiteness is retained, and the ray of finite blocks has one end.
- **Falsifier:** A failure of local finiteness, one-endedness, K₄-freeness, or exact cover number in the bridge-chain construction.
- **Lean mission:** `exists_connected_locallyFinite_oneEnded_K4free_triangleCover_omega`
- **Novelty query:** `"locally finite K4-free graph" countable triangle cover number omega`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `84/100`
- **Claim hash:** `ff6eae4da6dbcf85544914c2d89e1a2d2b8b4a9eb019f3189a750d5f07ebbb37`

#### T34 — Bounded-degree cover bound

- **Statement:** If a graph G has finite maximum degree Δ, then tc(G)≤⌈log₂(Δ+1)⌉.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** A graph of maximum degree Δ is (Δ+1)-colorable; apply T08/T10.
- **Falsifier:** A bounded-degree graph exceeding the stated cover bound.
- **Lean mission:** `triangleCover_le_ceillog_maxDegree_add_one`
- **Novelty query:** `"maximum degree" triangle-free edge cover logarithm`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `72/100`
- **Claim hash:** `62c2a5d689ff1768fc41017f24c3b1f4c66777006cd5821e0396e094f7d6a07b`

#### T35 — Unbounded-degree necessity for exact-ℵ₀ locally finite cores

- **Statement:** Every locally finite graph H with tc(H)=ℵ₀ has unbounded vertex degrees.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** If degrees were bounded by a finite Δ, T34 would make tc(H) finite.
- **Falsifier:** A locally finite bounded-degree graph with exact ℵ₀ triangle-cover number.
- **Lean mission:** `triangleCover_omega_implies_unbounded_degree`
- **Novelty query:** `"locally finite graph" unbounded degree triangle cover`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `68/100`
- **Claim hash:** `508f870d5991cad182879fa3fee430c4bc04d4f9b483cfc33f969af50cf74353`

#### T36 — Finite critical-density consequence

- **Statement:** If a finite graph G satisfies tc(G)>k, then G contains a subgraph H with minimum degree at least 2^k.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** T11 gives χ(G)>2^k. Take a vertex-critical subgraph H with the same chromatic number; every vertex of H has degree at least χ(H)-1≥2^k.
- **Falsifier:** A finite graph with tc>k whose every subgraph has a vertex of degree below 2^k.
- **Lean mission:** `finite_triangleCover_gt_has_minDegree_subgraph`
- **Novelty query:** `"triangle-free edge color number" minimum degree critical graph`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `86/100`
- **Claim hash:** `a115725ecece7a564edc90c4bb3bb18a8f5231a477a59146b9e5694e7d1a2d42`

#### T37 — Finite dense obstructions inside every witness

- **Statement:** Every Erdős #595 witness contains, for each positive integer k, a finite K₄-free subgraph having minimum degree at least 2^k.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Use T27 to find a finite K₄-free subgraph with tc>k, then apply T36 inside it.
- **Falsifier:** A witness lacking the required finite dense obstruction for some k.
- **Lean mission:** `erdos595_contains_finite_high_minDegree_K4free`
- **Novelty query:** `"Erdos 595 witness" finite subgraphs high minimum degree`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `91/100`
- **Claim hash:** `5846d6eda5013e07532e62cdb576e349c89b13dba3cbfbebbccd4f4465d98cc6`

### Package C — Chromatic dispersion and transversal collapse

#### T38 — Product-coloring lemma

- **Statement:** If E(G)=⋃_{i∈I}E(H_i) and each H_i has a proper vertex coloring with μ_i colors, then χ(G)≤∏_{i∈I} μ_i.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Color each vertex v by the tuple of its colors in all H_i. Every edge belongs to some H_i and is separated in that coordinate.
- **Falsifier:** A covered edge whose endpoints receive identical product profiles.
- **Lean mission:** `chromatic_le_product_of_edgeCover_colorings`
- **Novelty query:** `"product coloring" edge cover subgraphs chromatic number`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `90/100`
- **Claim hash:** `f8688ef888efc9e6c84e0058805528a51b078360fb36f8dd15dc455e5edf3750`

#### T39 — Uniform product bound

- **Statement:** If G is the union of κ subgraphs each of chromatic number at most μ, then χ(G)≤μ^κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Uniform specialization of T38.
- **Falsifier:** A κ-layer μ-colorable cover with χ(G)>μ^κ.
- **Lean mission:** `chromatic_le_pow_of_uniform_edgeCover`
- **Novelty query:** `"union of k subgraphs" chromatic number product bound`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `87/100`
- **Claim hash:** `70cc97b90cf28fefbb65ed755e34d0142da2162813e93df645064b4fa398f76d`

#### T40 — Triangle-free chromatic ceiling

- **Statement:** Define τ(G)=sup{χ(H):H⊆G and H is triangle-free}. If tc(G)≤κ, then χ(G)≤τ(G)^κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Apply T39 to a κ-layer triangle-free cover, using τ(G) as a uniform chromatic bound.
- **Falsifier:** A κ-layer triangle-free cover whose product coloring uses too few colors.
- **Lean mission:** `chromatic_le_triangleFreeCeiling_pow_cover`
- **Novelty query:** `"triangle-free subgraphs chromatic ceiling" cover number`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `98/100`
- **Claim hash:** `4f74e62e86053dc3b0a08fb8e104777b83e3204bdd31cbba7fa23e44afd352d4`

#### T41 — Chromatic-dispersion obstruction

- **Statement:** For every graph G and cardinal κ, χ(G)>τ(G)^κ implies tc(G)>κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Contrapositive of T40.
- **Falsifier:** A graph with the stated strict chromatic gap but a κ-layer triangle-free cover.
- **Lean mission:** `triangleCover_gt_of_chromatic_gt_tau_pow`
- **Novelty query:** `"chromatic gap triangle-free subgraphs" countable cover`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `100/100`
- **Claim hash:** `d19f3adf0f5dd41451718775da47c61c375459b44397f4a347761c32c979fc88`

#### T42 — Countable-power fixed-point close lemma

- **Statement:** If κ^{ℵ₀}=κ and a graph G satisfies χ(G)=κ^+ and τ(G)≤κ, then tc(G)>ℵ₀.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** T40 would give χ(G)≤κ^{ℵ₀}=κ under a countable cover, contradicting χ(G)=κ^+.
- **Falsifier:** A graph satisfying all cardinal hypotheses yet admitting a countable triangle-free cover.
- **Lean mission:** `fixedPoint_dispersion_solves_countableCover`
- **Novelty query:** `"kappa^omega=kappa" K4-free graph triangle-free subgraphs chromatic`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `100/100`
- **Claim hash:** `c8b7636f431312c28376af33dfd2bbf9c2d4b8164c1439b4b1dae3028b17b152`

#### T43 — Continuum-gap close lemma

- **Statement:** If χ(G)=(2^{ℵ₀})^+ and every triangle-free subgraph of G has chromatic number at most 2^{ℵ₀}, then G is not a countable union of triangle-free subgraphs.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Apply T42 with κ=2^{ℵ₀}, noting (2^{ℵ₀})^{ℵ₀}=2^{ℵ₀}.
- **Falsifier:** A continuum-gap graph with a countable cover.
- **Lean mission:** `continuumGap_implies_erdos595_property`
- **Novelty query:** `"continuum successor chromatic" triangle-free subgraphs continuum`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `100/100`
- **Claim hash:** `b25d92c850abc79654948c784c22d8af5e663360e3da9e26d6b86cb911fd7e49`

#### T44 — Finite-layer dispersion criterion

- **Statement:** If every triangle-free subgraph of a finite graph G is μ-colorable and χ(G)>μ^k, then tc(G)>k.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Finite specialization of T41.
- **Falsifier:** A k-layer cover contradicting the product-coloring bound.
- **Lean mission:** `finite_dispersion_implies_triangleCover_gt`
- **Novelty query:** `"finite graph" chromatic gap triangle-free subgraphs cover`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `85/100`
- **Claim hash:** `bcfbbbd446e66c330268881a62db30b2d3a547e4e9ee2b168c24083bb9f218fb`

#### T45 — Triangle-transversal formula for τ

- **Statement:** For every graph G, τ(G)=sup{χ(G−D):D⊆E(G) meets every triangle of G}.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** A spanning subgraph is triangle-free exactly when its deleted edge set meets every triangle. Nonspanning triangle-free subgraphs can be made spanning by adding isolated vertices without changing chromatic number.
- **Falsifier:** A triangle-free subgraph not representable by deleting a triangle transversal, or vice versa.
- **Lean mission:** `triangleFreeCeiling_eq_sup_transversalDeletion`
- **Novelty query:** `"triangle transversal" chromatic number after edge deletion`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `92/100`
- **Claim hash:** `3ac62d9bd3ea0f226013410eeb0a227f8900988e52cbb4431afe168f7e4f00c4`

#### T46 — Transversal-collapse criterion

- **Statement:** For cardinals μ, τ(G)≤μ if and only if every triangle transversal D of G satisfies χ(G−D)≤μ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Immediate from T45.
- **Falsifier:** A transversal deletion leaving chromatic number above μ while τ≤μ, or a high-χ triangle-free subgraph with no corresponding transversal.
- **Lean mission:** `tau_le_iff_all_transversal_deletions_chromatic_le`
- **Novelty query:** `"every triangle hitting set" chromatic collapse`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `94/100`
- **Claim hash:** `64844d7c1be2ed030d6f0d153b0e4c5df7d28193d5bc8e53157dd7f1fb8062b8`

#### T47 — General H-free product bound

- **Statement:** Fix a graph H₀ and define τ_{H₀}(G)=sup{χ(F):F⊆G and F is H₀-free}. If G is the union of κ H₀-free subgraphs, then χ(G)≤τ_{H₀}(G)^κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Same product-coloring proof as T40.
- **Falsifier:** A cover by H₀-free layers violating the product bound.
- **Lean mission:** `HFreeCover_chromatic_product_bound`
- **Novelty query:** `"H-free subgraph cover" chromatic product bound`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `74/100`
- **Claim hash:** `5c0339ab3980810d52d1b16fd3a3f1bdda3178cc4e60d1faba2a9a49bee5c0d3`

#### T48 — General hereditary-class product bound

- **Statement:** Let C be any class of graphs closed under taking subgraphs, and let τ_C(G)=sup{χ(F):F⊆G and F∈C}. If E(G) is covered by κ subgraphs in C, then χ(G)≤τ_C(G)^κ.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Apply T38 to the C-layers.
- **Falsifier:** A hereditary class cover violating the product profile coloring.
- **Lean mission:** `hereditaryClassCover_chromatic_product_bound`
- **Novelty query:** `"cover by hereditary graph class" chromatic number product`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `76/100`
- **Claim hash:** `b656e4e6502033d80ba424c73631c77befa625113d14d65758f5dd29ed94d3bb`

#### T49 — Dispersion lower-bound parameter

- **Statement:** Let d_△(G) be the least cardinal κ such that χ(G)≤τ(G)^κ. Then d_△(G)≤tc(G).
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** T40 shows every admissible triangle-cover cardinal is also admissible in the definition of d_△.
- **Falsifier:** A graph with d_△(G)>tc(G).
- **Lean mission:** `triangleDispersionExponent_le_triangleCover`
- **Novelty query:** `"dispersion exponent" triangle-free subgraphs chromatic`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `78/100`
- **Claim hash:** `d847b525f955a638c2e4386d4747d56692f398be238fb9e0deda43818ff7111c`

#### T50 — Exact-ℵ₀ core has countable vertex chromatic number

- **Statement:** If H has countably many edges and tc(H)=ℵ₀, then χ(H)=ℵ₀ after isolated vertices are discarded.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** T11 implies χ(H)>2^k for every finite k, so χ(H) is infinite. Countably many edges support only countably many nonisolated vertices, giving χ(H)≤ℵ₀.
- **Falsifier:** A countable-edge exact-ℵ₀ core with finite or uncountable chromatic number on its nonisolated part.
- **Lean mission:** `countable_exactOmega_triangleCover_has_chromatic_omega`
- **Novelty query:** `"countable graph" triangle cover omega chromatic omega`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `81/100`
- **Claim hash:** `e240ec159c8e6cfa029e49fc22ff77a635b9a1f113d78b3a318c50016eae0461`

#### T51 — K₄-free high-chromatic triangle-free-subgraph anchor

- **Statement:** Session-derived prior-art anchor: if G is K₄-free and χ(G)>2^{ℵ₀}, then G contains a triangle-free subgraph of uncountable chromatic number.
- **Status:** `SOURCE_DERIVED_PRIOR_ART_RECHECK_REQUIRED`
- **Proof route:** Recorded in the encirclement rounds as a Komjáth–Shelah theorem; do not promote until the local literature binder verifies the exact statement and hypotheses.
- **Falsifier:** An exact source showing a weaker cardinal threshold, different clique hypothesis, or failure of the claimed implication.
- **Lean mission:** `KS_highChromatic_K4free_has_uncountablyChromatic_triangleFree`
- **Novelty query:** `"K4-free" chromatic above continuum triangle-free uncountable chromatic Komjath Shelah`
- **Prior-art risk:** `LOW`
- **Structural leverage:** `88/100`
- **Claim hash:** `21334eef8c7c53f1036939d1071006398c2e127bdf1a71d4cf9a67c6893043c2`

### Package D — Triangle-hypergraph structure and realizability

#### T52 — Triangle hypergraphs are linear 3-uniform

- **Statement:** For every simple graph G, Tri(G) is a 3-uniform linear hypergraph: every hyperedge has three vertices and any two distinct hyperedges intersect in at most one vertex.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Graph triangles have three edges. Two distinct triangles sharing two graph edges would share the three endpoints and hence be the same triangle.
- **Falsifier:** A pair of distinct graph triangles sharing two distinct edges.
- **Lean mission:** `triangleHypergraph_uniform_linear`
- **Novelty query:** `"triangle hypergraph" linear 3-uniform`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `85/100`
- **Claim hash:** `03aeaf5632fb92c698a213b6f653c95d3b8faaae28a72bcad8868b39f7024ec7`

#### T53 — K₄–Berge-triangle equivalence

- **Statement:** A simple graph G is K₄-free if and only if Tri(G) contains no Berge 3-cycle, meaning no three triangle-hyperedges pairwise intersect in three distinct graph-edge vertices.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** A K₄ supplies three such triangles. Conversely, two graph triangles sharing an edge form a diamond; a third triangle sharing one distinct edge with each must add the missing edge of that diamond, producing a K₄.
- **Falsifier:** A K₄-free graph whose triangle hypergraph has a Berge 3-cycle, or a K₄ with none.
- **Lean mission:** `K4free_iff_triangleHypergraph_no_BergeC3`
- **Novelty query:** `"K4-free graph" triangle hypergraph Berge triangle`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `98/100`
- **Claim hash:** `c0ae4477a03907169f8a3a98e52a2a58075f53584af6b9856361c216bb3bf031`

#### T54 — Common-neighbor independence

- **Statement:** If G is K₄-free and uv∈E(G), then the common neighborhood N(u)∩N(v) is an independent set.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Adjacent common neighbors x,y together with u,v induce a K₄.
- **Falsifier:** An adjacent pair of common neighbors in a K₄-free graph.
- **Lean mission:** `K4free_commonNeighbors_independent`
- **Novelty query:** `"K4-free" common neighborhood of edge independent`
- **Prior-art risk:** `LOW`
- **Structural leverage:** `67/100`
- **Claim hash:** `f5cb205525e7ffb8701ae552bd88688a1135b32c8ca24e7dfae07ae77401d6a2`

#### T55 — Triangle multiplicity is unbounded in K₄-free graphs

- **Statement:** For every positive integer m there exists a finite K₄-free graph containing an edge that belongs to exactly m triangles.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Take the book graph consisting of m triangles sharing one common spine edge, with all page vertices pairwise nonadjacent.
- **Falsifier:** A forced upper bound on triangles per edge in every K₄-free graph.
- **Lean mission:** `exists_K4free_edge_triangleMultiplicity`
- **Novelty query:** `"book graph" K4-free edge in many triangles`
- **Prior-art risk:** `LOW`
- **Structural leverage:** `75/100`
- **Claim hash:** `19b4cf5cecc0d80087a5d35c9866a5919457f044879006c46cdfab8d7563ec72`

#### T56 — Book graphs have triangle-cover number two

- **Statement:** For every m≥1, the m-page book graph B_m has tc(B_m)=2.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** It contains a triangle, so tc≥2. Color the spine edge with one color and every page edge with the other; no triangle is monochromatic.
- **Falsifier:** A book graph requiring more or fewer than two layers.
- **Lean mission:** `triangleCover_bookGraph_eq_two`
- **Novelty query:** `"book graph" edge coloring no monochromatic triangle two colors`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `59/100`
- **Claim hash:** `6b13fb5acdefbff0f6d6ba374affc6b2a028e7d7bc0d59ab8d50978f11695b2b`

#### T58 — Exact endpoint representation theorem

- **Statement:** A 3-uniform hypergraph H is isomorphic to Tri(G) for some simple graph G if and only if there exist a set X and an injective map ρ:V(H)→[X]^2 such that: (i) for every hyperedge {a,b,c} of H, the pairs ρ(a),ρ(b),ρ(c) are exactly the three 2-subsets of some 3-element subset of X; and (ii) every 3-element subset of X whose three pairs lie in ρ(V(H)) corresponds to a hyperedge of H.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Use graph vertices as X and graph edges as pair images for the forward direction. For the reverse direction, take G with edge set ρ(V(H)); clauses (i) and (ii) give exact equality of triangle hypergraphs.
- **Falsifier:** A hypergraph satisfying the pair representation but producing a missing or extra graph triangle.
- **Lean mission:** `triangleHypergraph_realizable_iff_endpointRepresentation`
- **Novelty query:** `"which hypergraphs are triangle hypergraphs of graphs" endpoint representation`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `95/100`
- **Claim hash:** `e4ead4341b98659619d24dec0d48e0efd18a48c75c283a944bababa2d8117982`

#### T59 — Triangle-hypergraph embedding theorem

- **Statement:** A 3-uniform hypergraph H embeds as a subhypergraph of Tri(G) for some simple graph G if and only if there exist X and an injective map ρ:V(H)→[X]^2 satisfying condition (i) of T58 for every hyperedge of H; extra graph triangles are permitted.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Drop the exactness condition (ii) from T58.
- **Falsifier:** A forward-compatible endpoint assignment that does not realize an embedding.
- **Lean mission:** `triangleHypergraph_embeddable_iff_weakEndpointRepresentation`
- **Novelty query:** `"3-uniform hypergraph" embed triangle hypergraph graph`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `85/100`
- **Claim hash:** `229bfe6cc1f01128158a044e0e90526f3344dcb69e99ec98b1ae2c38044fa06a`

#### T60 — Finite triangle-hypergraph realizability lies in NP

- **Statement:** The decision problem 'given a finite 3-uniform hypergraph H, is H isomorphic to Tri(G) for some finite simple graph G?' belongs to NP.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** For m=|V(H)|, a certificate lists two endpoint labels for each hypergraph vertex using at most 2m labels. Verify injectivity and both conditions of T58 in polynomial time.
- **Falsifier:** A realizable instance requiring more than 2m endpoint labels or a certificate not polynomially checkable.
- **Lean mission:** `finite_triangleHypergraphRealizability_in_NP`
- **Novelty query:** `"triangle hypergraph realizability" computational complexity NP`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `83/100`
- **Claim hash:** `874fdf5f5452bb460f4361da80c2a10af69024b54408cf3d792e57cf98d1a5a9`

#### T61 — K₄-free realization certificate

- **Statement:** If a finite 3-uniform hypergraph H has an exact endpoint representation as in T58 and H has no Berge 3-cycle, then the realizing graph G is K₄-free.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Apply T53 to Tri(G)≅H.
- **Falsifier:** A Berge-C3-free exactly realized H whose realizing graph contains K₄.
- **Lean mission:** `endpointRepresentation_noBergeC3_gives_K4free`
- **Novelty query:** `"Berge triangle free hypergraph" K4-free graph realization`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `90/100`
- **Claim hash:** `4b11bf0fe9fe41ddada1ded428757ac57200b63c36396cae3d83a97ca00ad880`

#### T62 — Line-graph plus Krausz-partition recovery

- **Statement:** Given the line graph L(G) together with its canonical Krausz family of cliques corresponding to stars at vertices of G, Tri(G) consists exactly of the 3-cliques of L(G) that are not contained in a single star clique.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Three pairwise adjacent graph edges either share one common endpoint (a star triangle in L(G)) or form a graph triangle. The Krausz data distinguishes the two cases.
- **Falsifier:** A 3-clique of a line graph that is neither a common star nor a graph triangle.
- **Lean mission:** `triangleHypergraph_from_lineGraph_Krausz`
- **Novelty query:** `"line graph Krausz partition" recover graph triangles`
- **Prior-art risk:** `MEDIUM`
- **Structural leverage:** `78/100`
- **Claim hash:** `ff768f8cdff8d736689cdfbb1174b3255e115d8b8ca716b12324f90d91c0a0e6`

#### T63 — Realizable-hypergraph witness reduction

- **Statement:** If H is an uncountably chromatic 3-uniform hypergraph with no Berge 3-cycle and H is exactly realizable as Tri(G), then G is a K₄-free Erdős #595 witness.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** T53 gives K₄-freeness and T02 gives tc(G)=χ(H)>ℵ₀.
- **Falsifier:** A realization for which either K₄-freeness or cover number fails.
- **Lean mission:** `realizable_uncountablyChromatic_noBergeC3_solves_erdos595`
- **Novelty query:** `"uncountably chromatic linear hypergraph no Berge triangle graph realization`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `100/100`
- **Claim hash:** `6b63d9cbfbe000b17d80a32b5bf6dbf1448142b31da8406eeed95b8c1d564665`

#### T64 — Embedded-hypergraph witness reduction

- **Statement:** If H is an uncountably chromatic 3-uniform hypergraph that embeds into Tri(G), and G is independently known to be K₄-free, then G is an Erdős #595 witness.
- **Status:** `PROVED_IN_PACKET`
- **Proof route:** Hypergraph chromatic number is monotone under subhypergraphs, so χ(Tri(G))≥χ(H)>ℵ₀; use T02.
- **Falsifier:** A subhypergraph embedding with larger chromatic number than its host.
- **Lean mission:** `embedded_uncountablyChromatic_hypergraph_solves_erdos595`
- **Novelty query:** `"embed uncountably chromatic hypergraph into triangle hypergraph`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `96/100`
- **Claim hash:** `2b6069c3b523d2c9d5bd29b06c7743cb00307b1bea3bdddfa7ce1dd0c14d259f`

#### T65 — Broad realizability bridge

- **Statement:** Conditional theorem: if every linear Berge-C3-free 3-uniform hypergraph admits an exact endpoint representation, then Erdős #595 is equivalent to the existence of an uncountably chromatic linear Berge-C3-free 3-uniform hypergraph.
- **Status:** `CONDITIONAL_REDUCTION`
- **Proof route:** One direction uses T52–T53. The other uses the hypothesized realization theorem and T63.
- **Falsifier:** A finite or infinite linear Berge-C3-free hypergraph with no exact endpoint representation.
- **Lean mission:** `broad_realizability_reduces_erdos595`
- **Novelty query:** `"linear Berge-triangle-free hypergraph realizability as graph triangles`
- **Prior-art risk:** `HIGH`
- **Structural leverage:** `91/100`
- **Claim hash:** `63fb20072847269eddc9bc76c63bcc7ef4ec6f3202357b79bd0b4cf5d5f3089a`

#### T66 — Triangle-degree bound refutation

- **Statement:** The assertion 'every edge of a K₄-free graph belongs to at most a fixed constant number of triangles' is false, even for finite graphs.
- **Status:** `REFUTED_ROUTE`
- **Proof route:** T55 supplies m-page books for arbitrary m.
- **Falsifier:** A universal constant surviving the book family.
- **Lean mission:** `refute_bounded_triangleMultiplicity_K4free`
- **Novelty query:** `"K4-free graph" edge contained in arbitrarily many triangles`
- **Prior-art risk:** `LOW`
- **Structural leverage:** `80/100`
- **Claim hash:** `b85018aa58961f47a3c5dbe1e465f0678620a46fe3cb3f70cfc430ea288a9bc3`

---

## 4. Finite and computational theorem targets

These are exact, bounded research contracts suitable for SAT/CP-SAT, isomorph-free enumeration, independent verification, and certificate replay. No finite result may be promoted into an unbounded claim.

### C01 — Finite vertex threshold f(k)

- **Exact target:** For each k≥2, determine the least n for which there exists a K₄-free n-vertex graph G with tc(G)>k.
- **Required certificate:** SAT witness for the upper bound; DRAT/LRAT or exhaustive canonical-graph certificate for n−1 nonexistence.
- **Novelty query:** `"edge Folkman number" K4-free no monochromatic triangle k colors minimum vertices`
- **Priority:** `100/100`
- **Target hash:** `c3ffa049d52af7ed46be89e367e27a0df5d5b8a9543b3634919d7c1a8f71ccf1`

### C02 — Finite edge threshold m(k)

- **Exact target:** For each k≥2, determine the minimum number of edges in a K₄-free graph G with tc(G)>k.
- **Required certificate:** Explicit adjacency list plus independent checker; certified unsatisfiability below the edge threshold.
- **Novelty query:** `"minimum edges K4-free graph" multicolor triangle Ramsey edge coloring`
- **Priority:** `94/100`
- **Target hash:** `da31da5d6dc49d44b6c342b7495f8638895894285cef7a6d7515142679a0cae0`

### C03 — Maximum cover number at order n

- **Exact target:** Compute M(n)=max{tc(G):|V(G)|=n and G is K₄-free} for successive n.
- **Required certificate:** Complete isomorph-free enumeration or SAT optimization with independently checked extrema.
- **Novelty query:** `"maximum triangle cover number K4-free n vertices`
- **Priority:** `96/100`
- **Target hash:** `a8f205226da270a4866c2ced8e73fffcdb16752f6616d631aa98c90963cf263f`

### C04 — Extremizer classification

- **Exact target:** For every n where M(n) is known, classify all K₄-free n-vertex graphs attaining M(n).
- **Required certificate:** Canonical labels and completeness certificate.
- **Novelty query:** `"extremal K4-free graphs" monochromatic triangle edge coloring`
- **Priority:** `86/100`
- **Target hash:** `9f582f758961f2a740f8838496ffdcd1917d905d7c1a0dc3c175c3fb4c2e9b79`

### C05 — Finite chromatic-dispersion ratio

- **Exact target:** Among K₄-free n-vertex graphs, maximize χ(G)/max(1,τ(G)) and classify extremizers.
- **Required certificate:** Exact chromatic and τ certificates for every candidate plus global optimization proof.
- **Novelty query:** `"chromatic dispersion" triangle-free subgraph maximum chromatic number finite`
- **Priority:** `89/100`
- **Target hash:** `1f188a2266252e8e9eab16bb74afc145924bc8706a9cc58dccd44705a8559e09`

### C06 — Finite additive dispersion

- **Exact target:** Among K₄-free n-vertex graphs, maximize χ(G)−τ(G) and classify equality cases.
- **Required certificate:** Exact coloring certificates and exhaustive upper bound.
- **Novelty query:** `"K4-free graph" difference chromatic number triangle-free subgraph`
- **Priority:** `91/100`
- **Target hash:** `3826ee251844d331b0e734d7be64aea42a36069e262af9ad428343f2f84a5e5a`

### C07 — Triangle-transversal collapse profile

- **Exact target:** For a finite graph G define P_G(s)=max{χ(G−D):D is a triangle transversal and |D|≤s}. Compute P_G for all K₄-free graphs through a chosen order.
- **Required certificate:** Enumerated transversals, exact chromatic certificates, and canonical graph hashes.
- **Novelty query:** `"triangle transversal" chromatic collapse profile`
- **Priority:** `84/100`
- **Target hash:** `8ecf11f28d4c1847348f7e5db1f72cb87d3edb2515ed01b48ab0a857893dc79a`

### C08 — Minimum collapse transversal

- **Exact target:** Given finite G and r, determine the minimum |D| such that D meets every triangle and χ(G−D)≤r.
- **Required certificate:** Integer-program/SAT witness and dual lower-bound certificate.
- **Novelty query:** `"triangle hitting set" reduce chromatic number edge deletion`
- **Priority:** `83/100`
- **Target hash:** `abe4461c5dc084e5ebe105b52609fc74a1d2ace2ea5c6bc5355ea2228df5f1f6`

### C09 — K₄-safe amplification operation search

- **Exact target:** Search a registered family of graph products, substitutions, and amalgams for an operation ⋆ satisfying K₄-preservation while making χ(A⋆B) grow faster than τ(A⋆B).
- **Required certificate:** Machine-checked product definitions, K₄ witnesses/refutations, and exact χ/τ tables on sealed seeds.
- **Novelty query:** `"graph product" K4-free chromatic number triangle-free subgraphs amplification`
- **Priority:** `98/100`
- **Target hash:** `853389f4067a182b533b4983ded024fb91762baf2962ca0b49231c175b4f141c`

### C10 — Small-seed dispersion census

- **Exact target:** Enumerate small K₄-free seeds F with tc(F), χ(F), τ(F), transversal profiles, and all registered product iterates through a bounded size.
- **Required certificate:** Reproducible graph enumeration and independent invariant checkers.
- **Novelty query:** `"finite K4-free graph" chromatic dispersion seed`
- **Priority:** `88/100`
- **Target hash:** `9012feb7025ac136b273f855f7dc0ecd6815dafbad8500773542afc2c804e020`

### C11 — Smallest nonrealizable linear Berge-C3-free hypergraph

- **Exact target:** Find the minimum m for which a linear Berge-C3-free 3-uniform hypergraph on m vertices has no exact endpoint representation.
- **Required certificate:** SAT unsatisfiability certificate for endpoint realization and exhaustive proof that all smaller instances are realizable.
- **Novelty query:** `"nonrealizable triangle hypergraph" linear 3-uniform Berge triangle free`
- **Priority:** `100/100`
- **Target hash:** `de38356930f0d651b448c13200cbf7d879fcbe7bcae654c2cff4228210d23ffb`

### C12 — Realizability classification

- **Exact target:** Classify all linear Berge-C3-free 3-uniform hypergraphs up to m vertices by exact endpoint realizability.
- **Required certificate:** Canonical hypergraph enumeration plus verified endpoint certificates or UNSAT proofs.
- **Novelty query:** `"classification triangle hypergraphs of graphs" finite hypergraphs`
- **Priority:** `94/100`
- **Target hash:** `906eaa5e8758e34592fef8d9e52ea42a80b424fbf97172781da64ebecb55ca29`

### C13 — Intersection-data insufficiency witness

- **Exact target:** Find the smallest pair H₁,H₂ of 3-uniform hypergraphs with isomorphic hyperedge-intersection graphs such that exactly one is endpoint-realizable.
- **Required certificate:** Two canonical hypergraphs, isomorphism certificate for intersection graphs, realization certificate for one, UNSAT certificate for the other.
- **Novelty query:** `"hyperedge intersection graph" triangle hypergraph realizability not determined`
- **Priority:** `90/100`
- **Target hash:** `501fe11a5be7f13204e8c87ac75860313abea15a0ccbbafd14c596caeda47eab`

### C14 — Endpoint SAT compiler

- **Exact target:** Implement and verify a SAT encoding of T58 with exactness, optional K₄-freeness, and extraction of the realizing graph.
- **Required certificate:** Round-trip tests, independent direct verifier, and certificate replay.
- **Novelty query:** `"SAT encoding triangle hypergraph graph realization`
- **Priority:** `95/100`
- **Target hash:** `7e22b3226c399eb2bee87d97a74f9059c843250accab22c4bebfc2090b5702be`

### C15 — Finite transversal centeredness spectrum

- **Exact target:** For each finite K₄-free graph G, compute the least number of triangle transversals with empty intersection and verify that it equals tc(G).
- **Required certificate:** Independent implementations of edge coloring and transversal-family optimization, compared on every graph.
- **Novelty query:** `"triangle transversal centeredness number" hypergraph chromatic`
- **Priority:** `97/100`
- **Target hash:** `9931cea6511a20a7b1d5d7cee873355d9ede9e977c579f1703e3793a9339625a`

### C16 — Minimal k-centered obstruction

- **Exact target:** For each finite k, find the smallest K₄-free graph whose triangle-transversal family is k-centered but not (k+1)-centered.
- **Required certificate:** Explicit graph and transversal family, plus certified absence below the threshold.
- **Novelty query:** `"k-wise intersecting triangle transversals" K4-free graph`
- **Priority:** `96/100`
- **Target hash:** `96bda5c7ae3e3f66af7296cead98dbdeea435d89dbdd99290ce4d5c82dca67f9`

### C17 — Near-extremal stability

- **Exact target:** For fixed n,k, classify K₄-free graphs with tc(G) within one of M(n), and test whether they are edit-close to the exact extremizers.
- **Required certificate:** Canonical edit-distance census and complete enumeration.
- **Novelty query:** `"stability theorem K4-free edge Ramsey triangle coloring`
- **Priority:** `75/100`
- **Target hash:** `bd3dad57fea8c4dd7564c86cadd7f1f6530dc7f690374e2b98cf0a5841f6eaaa`

### C18 — Countable-core constructor replay

- **Exact target:** Given a sequence of certified finite K₄-free graphs F_k with tc(F_k)>k, mechanically construct and verify the one-ended locally finite graph schema from T33.
- **Required certificate:** Finite-prefix checker plus symbolic proof that bridge gluing preserves all invariants.
- **Novelty query:** `"one-ended locally finite K4-free graph triangle cover omega`
- **Priority:** `82/100`
- **Target hash:** `e790ad3e6cbb3ea63fe9401ce1c8d88ec820a937bc70e2df002f5ef26ca4f525`

---

## 5. Forced flagship close programs

Every program ends at the exact flagship. A failed program is accepted only when it emits the single load-bearing missing theorem and a falsifier.

### P01 — Transversal-centeredness direct construction

**Program**

```text
1. Construct a K₄-free graph G.
2. Prove that every countable family of triangle transversals of G has nonempty intersection.
3. Apply T05 to obtain tc(G)>ℵ₀.
```

- **Load-bearing missing step:** An explicit ZFC construction whose full triangle-transversal family is countably centered.
- **Kill condition:** A countable family of transversals with empty intersection, equivalently an explicit countable triangle-free cover.
- **Flagship impact:** `100/100`
- **Program hash:** `904b4e90256241f7019518b07592606e569ff823481496d9d9862bd0380c24fd`

### P02 — Graph-realizable hypergraph route

**Program**

```text
1. Construct an uncountably chromatic linear 3-uniform hypergraph H with no Berge 3-cycle.
2. Produce an exact endpoint representation of H.
3. Apply T61 and T63.
```

- **Load-bearing missing step:** Simultaneous uncountable chromaticity, Berge-C3 avoidance, and endpoint realizability.
- **Kill condition:** Failure of endpoint constraints, a Berge 3-cycle, or a countable proper coloring.
- **Flagship impact:** `100/100`
- **Program hash:** `ce5f0858d7112ccd97d4910b33cbcea8f183aa521a883df246d5b46a9d2da42f`

### P03 — Cardinal-dispersion fixed-point route

**Program**

```text
1. Choose κ with κ^{ℵ₀}=κ.
2. Construct a K₄-free G with χ(G)=κ^+.
3. Prove τ(G)≤κ.
4. Apply T42.
```

- **Load-bearing missing step:** The K₄-free chromatic-dispersion construction at a countable-power fixed point.
- **Kill condition:** A triangle-free subgraph of chromatic number κ^+, or a κ-coloring of G.
- **Flagship impact:** `100/100`
- **Program hash:** `fb466c2bcb9495f8e2cead07a404f9e7d6195c6c1acde55af6c69302cfabe0ad`

### P04 — Generalized Komjáth–Shelah lift

**Program**

```text
1. Extract the exact finite-condition forcing and preservation lemmas from the known one-cardinal separation construction.
2. Replace (ℵ₀,ℵ₁) by (κ,κ^+) under explicit cardinal arithmetic.
3. Preserve χ(G)=κ^+ while forcing every triangle-free subgraph κ-colorable.
4. De-force or isolate the exact consistency-only step.
```

- **Load-bearing missing step:** A generalized fusion/preservation theorem and then a ZFC replacement for genericity.
- **Kill condition:** A support collision, chain-condition failure, or surviving high-chromatic triangle-free subgraph.
- **Flagship impact:** `99/100`
- **Program hash:** `391f81f63e3fb403c726b8f7101e3f11c2a74dd19b19a21faa857f8525085ac6`

### P05 — Minimal-cardinality reflection attack

**Program**

```text
1. Assume a witness and choose one of least vertex cardinal λ.
2. Use T24 to obtain cf(λ)>ℵ₀.
3. Build elementary or combinatorial approximations of size <λ.
4. Attempt to glue their countable covers into a global cover or isolate the exact failure.
```

- **Load-bearing missing step:** A reflection/gluing theorem at uncountable cofinality that respects cross-stage edges.
- **Kill condition:** An explicit coherent family of local covers whose cross-edge constraints cannot be synchronized.
- **Flagship impact:** `94/100`
- **Program hash:** `f5d935559acc90c954885f1c2bfd615c828136328e2f89bdfe125fa78369bbf8`

### P06 — Exact-ℵ₀ core extension

**Program**

```text
1. Start with the connected locally finite one-ended K₄-free core H from T33, where tc(H)=ℵ₀.
2. Extend H through >2^{ℵ₀} many controlled stages.
3. Preserve K₄-freeness.
4. Force every countable coloring of the final edge set to fail on some finite obstruction extending a banked H-pattern.
```

- **Load-bearing missing step:** A prediction/capture principle for future countable edge colorings that does not use an unearned forcing step.
- **Kill condition:** A countable coloring that assigns fresh colors across every activated finite obstruction.
- **Flagship impact:** `96/100`
- **Program hash:** `3216cc11f9a2557aa305c6df45ae35952e095dc6003b9a5971d07c8eba2b31f3`

### P07 — Genericity differencer / de-forcing

**Program**

```text
1. Parse the exact consistency proof into finite combinatorial lemmas and genericity-dependent lemmas.
2. Court-promote every finite lemma.
3. Identify the unique dense-set or bookkeeping statement actually using genericity.
4. Replace that statement by an explicit ZFC combinatorial principle.
```

- **Load-bearing missing step:** A ZFC replacement for the final genericity obligation.
- **Kill condition:** A proof that the isolated principle implies a known independent statement or cannot hold in ZFC.
- **Flagship impact:** `98/100`
- **Program hash:** `b61a6177596896568e67d6593a9717c938abbc7a15d2a0d1dafc5abaf10327b1`

### P08 — Direct countable-cover diagonalization

**Program**

```text
1. Conditions are finite K₄-free graphs with side data.
2. A requirement names a prospective countable sequence of triangle-free layers.
3. Extend a condition so that some edge is outside every named layer or one named layer gains a triangle.
4. Meet all requirements in a single ZFC recursion.
```

- **Load-bearing missing step:** A way to enumerate/capture all final countable covers without circularly knowing the final graph.
- **Kill condition:** A cover not approximated by any stage requirement.
- **Flagship impact:** `97/100`
- **Program hash:** `4fbcec6e87eae0e42319a56640644e10065aad30796e72ac2b1453a07e0d0ab0`

### P09 — Amplification plus incompactness

**Program**

```text
1. Find a finite K₄-safe operation ⋆ for which χ compounds faster than τ.
2. Prove sharp finite amplification.
3. Lift the finite separation to a graph of cardinal κ^+ while all <κ^+-sized stages remain κ-controlled.
4. Apply T42.
```

- **Load-bearing missing step:** An incompactness lift preserving the finite dispersion inequality.
- **Kill condition:** Collapse of χ, explosion of τ, or creation of K₄ under iteration.
- **Flagship impact:** `95/100`
- **Program hash:** `0e1ecec3b0d1470f2664a7257e839784dbb8253e3bcb716566737d794c379580`

### P10 — Broad realization theorem attack

**Program**

```text
1. Characterize orientation/endpoint consistency obstructions for linear Berge-C3-free hypergraphs.
2. Prove that an identified large subclass is exactly realizable.
3. Construct an uncountably chromatic member of that subclass.
4. Apply T63.
```

- **Load-bearing missing step:** A realizability theorem broad enough to contain an uncountably chromatic no-Berge-C3 example.
- **Kill condition:** A finite minimal nonrealizable obstruction present in every proposed subclass.
- **Flagship impact:** `93/100`
- **Program hash:** `e00fdbc15e5dc6c40f61076c6b544b056b8a2b6a89ca3a73e91677925d302d9a`

### P11 — Centered filter-base route

**Program**

```text
1. Use T05 to seek a K₄-free triangle system whose transversal family is countably centered.
2. Close this family under a controlled finite-intersection operation without losing nonemptiness.
3. Extract a structural filter-like object that directs a graph construction.
4. Decode it back into G.
```

- **Load-bearing missing step:** A closure operation strong enough to guide construction but weak enough not to require a countably complete ultrafilter or large-cardinal strength.
- **Kill condition:** A derivation of an actual countably complete free ultrafilter from the proposed axioms, indicating excessive consistency strength.
- **Flagship impact:** `90/100`
- **Program hash:** `226b26ce45d995c902100c20a9b6dbeb67f800f990c15e1ff0c53eb518d6814d`

### P12 — Compactness-spectrum route

**Program**

```text
1. Treat tc(G) as the chromatic compactness spectrum of Tri(G).
2. Bank T26 for every fixed finite k and T28 for the exact-ℵ₀ core.
3. Identify a graph-realizable no-Berge-C3 hypergraph in which finite compactness holds at every k but countable compactness fails.
4. Realize it as Tri(G).
```

- **Load-bearing missing step:** A specifically graph-realizable failure of compactness at ℵ₀, rather than an arbitrary uncountably chromatic hypergraph.
- **Kill condition:** Every candidate either becomes countably colorable or violates endpoint realizability/K₄-freeness.
- **Flagship impact:** `92/100`
- **Program hash:** `db8ca59868226690e22ad2611075fd66d2d5ee1e5021a7bd3539e0027799ef93`

---

## 6. Hostile quarantine: claims that must not re-enter Court

- **Q01 — Semantic reversal:** Replacing the existential question 'does a witness exist?' with the universal statement 'is every graph decomposable?' changes the target.
- **Q02 — Fake independence promotion:** A consistency result in one direction does not prove independence; both model directions and exact reductions are required.
- **Q03 — Unverified four-tuple shift graph:** The proposed interleaving graph was not proved K₄-free and no valid countable-color Ramsey argument was supplied.
- **Q04 — False bounded triangle multiplicity:** K₄-freeness does not bound the number of triangles through an edge; book graphs refute every constant bound.
- **Q05 — Unsupported local 2/3 theorem:** The Rödl-nibble invocation lacked its hypotheses, the local ratio was not coherently defined, and the key codegree assertion was false.
- **Q06 — Receipt/authority confusion:** Hash chains, compiler labels, and 'certificate checked' strings certify operational bytes only unless an independent mathematical checker is bound to the exact claim.
- **Q07 — Countable-direct-limit fantasy:** A countable union of finite graphs has countably many edges and is trivially countably triangle-decomposable.
- **Q08 — Finite-unbounded-to-uncountable leap:** Arbitrarily large finite cover numbers yield an exact-ℵ₀ countable core, not automatically a graph with cover number above ℵ₀.

---

## 7. Lean formalization queue

### Tier 1 — elementary reusable kernel

`T01`, `T02`, `T03`, `T04`, `T05`, `T07`, `T09`, `T10`, `T11`, `T14`, `T15`, `T16`, `T17`, `T19`, `T20`, `T31`, `T38`, `T39`, `T40`, `T41`, `T45`, `T46`, `T52`, `T53`, `T54`, `T56`, `T58`, `T59`, `T61`

These should be broken into finite-set, coloring, complement, and cardinal-product lemmas. `T04` is the most reusable abstraction: hypergraph colorings are dual to empty-intersection families of vertex covers.

### Tier 2 — compactness and cofinality

`T23`, `T24`, `T25`, `T26`, `T27`, `T28`, `T29`, `T42`, `T43`

These require a deliberate choice between mathlib cardinal/cofinality infrastructure and a smaller theorem interface imported as an assumption with a later kernel bridge.

### Tier 3 — finite certificate bridges

Formalize the soundness of:

- finite edge-coloring certificates for `tc(G)≤k`;
- SAT/DRAT certificates for `tc(G)>k`;
- endpoint-representation certificates for `T58–T61`;
- canonical graph/hypergraph serialization and isomorphism hashes;
- triangle-transversal certificates and the `T04/T05` duality checker.

### Suggested first Lean signatures

```lean
-- Names are design targets, not compilation claims.
theorem triangleCover_iff_nonmonochromatic_edgeColoring ...
theorem hypergraphChromatic_eq_min_emptyIntersection_vertexCovers ...
theorem triangleCover_gt_iff_transversals_centered ...
theorem bipartiteCoverNumber_eq_cardinalLog_chromatic ...
theorem triangleCover_le_of_chromatic_le_two_pow ...
theorem minimal_vertexCard_triangleCover_gt_cofinality ...
theorem chromatic_le_triangleFreeCeiling_pow_cover ...
theorem triangleFreeCeiling_eq_sup_transversalDeletion ...
theorem K4free_iff_triangleHypergraph_no_BergeC3 ...
theorem triangleHypergraph_realizable_iff_endpointRepresentation ...
```

---

## 8. Novelty-checker ingestion order

Run exact-claim novelty checks in this order:

1. `T04–T06`: blocker-centeredness/triangle-transversal duality and its finite/ω/>ω trichotomy.
2. `T23–T25`: minimal-cardinality cofinality theorems.
3. `T28–T29`, `T33`: exact-ω core extraction and the one-ended locally finite construction.
4. `T41–T49`: chromatic-dispersion parameter and transversal-collapse package.
5. `T53`, `T58–T62`: Berge-cycle characterization and endpoint/Krausz realizability language.
6. `C11–C16`: finite nonrealizability and centeredness classifications.

For every collision:

- delete novelty presumption;
- bind the strongest known statement;
- compute the exact difference;
- regenerate sharpenings, converses, equality cases, algorithms, and formalization contributions.

---

## 9. Immediate executable campaign

### Campaign A — Duality package

Formalize `T02`, `T04`, and `T05`; run novelty; then launch `C15–C16`. This package creates a new exact coordinate system for the flagship: not edge colorings, but countable centeredness of all triangle transversals.

### Campaign B — Realizability package

Implement `C14`, enumerate `C11–C13`, and use every minimal nonrealizable hypergraph as a permanent rejection boundary for `P02/P10`.

### Campaign C — Countable core package

Bind known finite Folkman witnesses, instantiate `T33`, and characterize how exact-ℵ₀ complexity is distributed along a one-ended locally finite graph. Then attack `P06`: what additional uncountable scaffold changes finite-intersection behavior into countable centeredness?

### Campaign D — Full close

Run `P01`, `P02`, `P03`, and `P07` in parallel. Force a complete proof after every accepted theorem or refutation. The active flagship wall is the construction of a K₄-free triangle system whose full transversal family is countably centered.

---

## 10. Final Court/Search inventory

- **Exact theorem cards:** `66`
- **Finite/computational targets:** `18`
- **Forced close programs:** `12`
- **Quarantined false/unsupported mechanisms:** `8`
- **Historical novelty claims:** `0`
- **Lean compilation claims:** `0`
- **Flagship closure claims:** `0`

### Strongest exact new campaign representation

\[
\boxed{\text{Find a }K_4\text{-free graph }G\text{ such that every countable family of triangle transversals has nonempty intersection.}}
\]

By `T05`, that statement is exactly equivalent to `tc(G)>ℵ₀`. By `T53`, K₄-freeness is exactly the absence of a Berge `C₃` in `Tri(G)`. Therefore the flagship may be attacked as:

\[
\boxed{\text{Construct a graph-realizable linear Berge-}C_3\text{-free 3-hypergraph whose vertex-cover family is countably centered.}}
\]

This is not a solution. It is an exact, lossless, theorem-generating coordinate system with direct Lean, SAT, novelty, and close-attempt interfaces.

---

**End of theorem refinery.**
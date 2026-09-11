# Erdős #738 × #595 cross theorem bank — cards 21–30 of 47

**Claim boundary:** These are theorem/target cards from the 2026-08-04 #738×#595 cross-encirclement packet. `PROVED_IN_PACKET` means an explicit proof route was supplied in the packet; conditional cards retain their stated dependency; `REFUTED_ROUTE` and `UNPROVED_CHECKABLE_TARGET` are not positive theorems. Historical novelty remains unadjudicated.

## XCONE06 — Conditional Forest-Bouquet Universality

**Status:** `CONDITIONAL_ON_738_SEQUENCE` · **Package:** B — Cone transfer · **Claim hash:** `1c149e39fff2cc24f65a6d384bcda878fcb286b042e919b29051c5e035a953a1`

Assume the triangle-free Gyárfás–Sumner statement for each tree in a sequence \(T_0,T_1,\dots\), where every \(T_i\) has at least two vertices. Then every #595 witness contains an induced
\[
K_1\vee\bigsqcup_{i<\omega}T_i.
\]

**Proof route:** Inside the infinite-chromatic triangle-free link from XLINK06, recursively find T_i and delete its closed neighborhood. The #738 protected-deletion lemma keeps the residual infinitely chromatic and makes the copies pairwise anticomplete.

**Falsifier:** A witness or sequence for which the recursive protected extraction fails.

**Lean mission:** `erdos595_contains_cone_over_tree_sequence`

## XCONE07 — All-Finite-Trees Bouquet Consequence

**Status:** `CONDITIONAL_ON_FULL_738` · **Package:** B — Cone transfer · **Claim hash:** `c35ccc2b5ec9416834eb8ebc3e23be8d59a73fdc8a6c1e1e7094a478151616d3`

If Erdős #738 holds for every finite tree, then every #595 witness contains an induced cone over a countable forest containing one component isomorphic to every finite tree.

**Proof route:** Enumerate the finite trees and apply XCONE06.

**Falsifier:** A full #738 proof and a #595 witness lacking the enumerating bouquet.

**Lean mission:** `full738_implies_595_universalTreeBouquet`

## XCONE08 — Cone Sterility Theorem

**Status:** `PROVED_IN_PACKET` · **Package:** B — Cone transfer · **Claim hash:** `b028f729e2dcc487528215f61d799319187b9d9476e7166fe56571a916d71eb5`

For every triangle-free graph \(H\) with at least one edge, \(K_1\vee H\) is \(K_4\)-free and has \(tc=2\), regardless of \(\chi(H)\) or the induced-tree complexity of \(H\).

**Proof route:** K4-freeness follows because H has no triangle. Two layers are the apex star and H; a triangle forces the lower bound two.

**Falsifier:** A triangle-free H whose cone contains K4 or needs more than two layers.

**Lean mission:** `cone_triangleFree_K4free_triangleCover_eq_two`

## XCONE09 — Type-Tensor Extremality Is Triangle-Cover Sterile

**Status:** `PROVED_IN_PACKET` · **Package:** B — Cone transfer · **Claim hash:** `43abcff75dc7f3c6f0a10d286e773b708b6e3fb668d461925de57bfd2ef1f839`

Coning the parity-defect hosts from the #738 type-tensor package produces \(K_4\)-free graphs with sharp/extremal type-defect tensors in their links but triangle-cover number exactly \(2\).

**Proof route:** The parity-defect host is triangle-free by the #738 bank; apply XCONE08.

**Falsifier:** A parity-host cone whose cover number exceeds two.

**Lean mission:** `parityTensor_cone_triangleCover_two`

## XCONE10 — Local-Complexity Non-Sufficiency

**Status:** `REFUTED_ROUTE` · **Package:** B — Cone transfer · **Claim hash:** `7dd65d9ef017adb55ec432740280b96830f6ca14ff6f1573317e9b0ede25a116`

No lower bound on the chromatic number, criticality, induced-tree richness, or type-tensor complexity of a single \(K_4\)-free vertex link can by itself imply \(tc(G)>2\).

**Proof route:** XCONE08 realizes arbitrary triangle-free link complexity inside a two-layer cone.

**Falsifier:** A proposed single-link invariant that excludes all cone examples and still claims universality.

**Lean mission:** `singleLinkComplexity_not_sufficient_for_highTriangleCover`

## XLAYER01 — Tree-Rich Layer Product Theorem

**Status:** `CONDITIONAL_ON_738_T` · **Package:** C — Layer hierarchy · **Claim hash:** `e79779ab3472952c72c429a665e6afb545972ce066f81e910fd152099552e2c6`

Fix a finite tree \(T\) and suppose every triangle-free induced-\(T\)-free graph is \(c\)-colorable. If \(E(G)=\bigcup_{i<m}E(H_i)\) with every \(H_i\) triangle-free and induced-\(T\)-free, then \(\chi(G)\le c^m\).

**Proof route:** Properly c-color each H_i and take the product coloring of their vertex colorings.

**Falsifier:** An m-layer cover violating the product coloring.

**Lean mission:** `treeFree_triangleLayerCover_chromatic_pow_bound`

## XLAYER02 — Finite-Layer Forced-Tree Corollary

**Status:** `CONDITIONAL_ON_738_T` · **Package:** C — Layer hierarchy · **Claim hash:** `2bae11e04ea67c19aaaa48e817a4183f722f984f14240a30331dd3882d7ac05f`

Under the same #738(T) hypothesis, if \(G\) has a cover by \(m\) triangle-free subgraphs and \(\chi(G)>c(T)^m\), then every such cover has at least one layer containing an induced \(T\).

**Proof route:** Contrapositive of XLAYER01.

**Falsifier:** A high-chromatic m-cover whose every layer is induced-T-free.

**Lean mission:** `highChromatic_finiteTriangleCover_forces_treeInLayer`

## XLAYER03 — Countable-Layer Forced-Tree Corollary

**Status:** `CONDITIONAL_ON_738_T` · **Package:** C — Layer hierarchy · **Claim hash:** `694543d0056f1f24197ba4c68ca4baada8cd307452bf38ec7014f4fce9419477`

Under #738(T), if \(G\) is countably covered by triangle-free subgraphs and \(\chi(G)>c(T)^{\aleph_0}\), then every countable cover has a layer containing an induced \(T\).

**Proof route:** Countable product version of XLAYER01.

**Falsifier:** A countable cover of a graph above the product bound with every layer T-free.

**Lean mission:** `countableTriangleCover_highChromatic_forces_treeLayer`

## XLAYER04 — Ambient Defect-Layer Inheritance

**Status:** `PROVED_IN_PACKET` · **Package:** C — Layer hierarchy · **Claim hash:** `7dd6976d75ff71e6ab204d3757b7700ee43b7c3b30fdfe04ad657d623dc5b238`

Suppose \(G=\bigcup_{i<m}H_i\), each \(H_i\) is triangle-free, and \(H_j[X]\) is an induced copy of a tree \(T\). Then every ambient extra edge in \(G[X]\setminus E(T)\) is covered by the other \(m-1\) layers. Hence the ambient defect graph on \(X\) has triangle-cover number at most \(m-1\).

**Proof route:** An extra edge is absent from H_j by inducedness, so it must occur in another covering layer.

**Falsifier:** An ambient defect edge belonging only to the tree layer.

**Lean mission:** `layerInducedTree_defectCover_descends`

## XLAYER05 — Defect-Depth Descent

**Status:** `PROVED_IN_PACKET` · **Package:** C — Layer hierarchy · **Claim hash:** `8ecd80666a008c7e021b7c8c6a429b587094cabc045467392a4f416c1b6b4e94`

In an \(m\)-layer triangle-free cover, every tree induced in one layer has an ambient defect graph of cover depth at most \(m-1\). Therefore ambient purification can be organized as an induction on layer depth, with \(m=1\) as the exact induced base case.

**Proof route:** Repackage XLAYER04 as an inductive invariant.

**Falsifier:** A layer-induced tree whose ambient defect graph requires m or more layers.

**Lean mission:** `ambientTreeDefect_depth_lt_coverDepth`

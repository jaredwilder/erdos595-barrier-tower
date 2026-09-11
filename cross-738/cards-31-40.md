# Erdős #738 × #595 cross theorem bank — cards 31–40 of 47

**Claim boundary:** These are theorem/target cards from the 2026-08-04 #738×#595 cross-encirclement packet. `PROVED_IN_PACKET` means an explicit proof route was supplied in the packet; conditional cards retain their stated dependency; `REFUTED_ROUTE` and `UNPROVED_CHECKABLE_TARGET` are not positive theorems. Historical novelty remains unadjudicated.

## XLAYER06 — Induced-Tree-Free Layer-Cover Bound

**Status:** `CONDITIONAL_ON_738_T` · **Package:** C — Layer hierarchy · **Claim hash:** `80ddf577559ebb577e3cd8dbda5060fdbb04b6cd4b475a870531c1d782d14486`

Let \(itc_T(G)\) be the least cardinality of a cover of \(E(G)\) by subgraphs that are both triangle-free and induced-\(T\)-free. Under #738(T) with bound c,
\[
\chi(G)\le c^{\,itc_T(G)}.
\]

**Proof route:** Apply the product-coloring lemma to a minimum such cover.

**Falsifier:** A cover by induced-T-free triangle-free layers violating the product bound.

**Lean mission:** `inducedTreeFreeTriangleCover_productBound`

## XLAYER07 — Induced-Free Refinement Failure

**Status:** `PROVED_IN_PACKET` · **Package:** C — Layer hierarchy · **Claim hash:** `456f3e6056860d0afb6fed00df2704ff4d4d526caf1b59f70af74bd9d442335b`

The cover-to-partition refinement used for ordinary triangle-free layers does not extend to induced-tree-free layers in general. Specifically, \(C_4\) is triangle-free and induced-\(P_4\)-free, while deleting one edge produces an induced \(P_4\).

**Proof route:** The displayed four-vertex example is an explicit counterexample to downward closure under edge deletion.

**Falsifier:** A claim that every subgraph of an induced-P4-free triangle-free graph remains induced-P4-free.

**Lean mission:** `inducedTreeFree_cover_refinement_failure_P4`

## XLAYER08 — No Automatic Blocker Duality for \(itc_T\)

**Status:** `REFUTED_ROUTE` · **Package:** C — Layer hierarchy · **Claim hash:** `ae41b5ae5c353f950e726139a01722a5a03aefb4902faa9de6c275f45f3445d0`

Because induced-\(T\)-freeness is not generally preserved by deleting edges, the blocker-centeredness duality and least-layer partition refinement for \(tc(G)\) cannot be imported unchanged to \(itc_T(G)\).

**Proof route:** XLAYER07 kills the required downward-closure step.

**Falsifier:** A valid general refinement theorem overcoming the explicit C4/P4 obstruction.

**Lean mission:** `no_naive_blockerDuality_inducedTreeFreeLayers`

## XLAYER09 — Hereditary Edge-Deletion Layer Refinement

**Status:** `PROVED_IN_PACKET` · **Package:** C — Layer hierarchy · **Claim hash:** `82d878650cb34ed5db5064803fbf529a225e37f6a1298b0fdb6f3fa557ba40db`

For any class of edge sets closed under taking subsets, every cover by \(\kappa\) members of the class refines to a partition by \(\kappa\) members. In particular, covers by triangle-free and non-induced-\(T\)-subgraph-free layers refine to partitions.

**Proof route:** Assign each edge to its least covering layer; subset closure preserves membership.

**Falsifier:** A subset-closed class for which least-layer refinement leaves the class.

**Lean mission:** `subsetClosed_layerCover_refines_partition`

## XLAYER10 — Finite-Layer Gyárfás Hierarchy

**Status:** `UNPROVED_CHECKABLE_TARGET` · **Package:** C — Layer hierarchy · **Claim hash:** `a27352650a03fc43a637ed3fd5e31a191d47acb66eb7a2f7be1434e99fab5dc6`

Conjectural target: for every finite tree \(T\) and integer \(m\ge1\), there is \(f(T,m)\) such that every graph with \(tc(G)\le m\) and \(\chi(G)>f(T,m)\) contains an induced \(T\). The case \(m=1\) is Erdős #738.

**Proof route:** Use XLAYER04–XLAYER05 to attack the ambient defect graph inductively.

**Falsifier:** A fixed m and tree T with unbounded-chromatic induced-T-free graphs of tc≤m.

**Lean mission:** `finiteLayer_gyarfasHierarchy`

## XLAYER11 — Two-Layer Purification Target

**Status:** `UNPROVED_CHECKABLE_TARGET` · **Package:** C — Layer hierarchy · **Claim hash:** `d0b3d71e1e9e4649867b88c85ac1720588f4b81091978f83b7ddb3eaf6f8d31c`

The first hybrid frontier is \(m=2\): classify when a tree induced in one triangle-free layer can have its entire ambient defect graph contained in one triangle-free layer without admitting an induced copy after reselection.

**Proof route:** Encode the second-layer defect graph with the #738 contact-signature and type-tensor machinery.

**Falsifier:** A complete classification, or a smallest counterexample to the proposed purification mechanisms.

**Lean mission:** `twoLayer_treePurification`

## XLAYER12 — Layer-Colored Defect Tensor Target

**Status:** `UNPROVED_CHECKABLE_TARGET` · **Package:** C — Layer hierarchy · **Claim hash:** `d6cd847f5302303f2a804dd4c9097e8e86b44de589a48541a3e8c3a307d7901d`

For type-uniform path-induced tree copies inside one layer, refine the #738 Boolean defect tensor to an \((m-1)\)-colored tensor recording the first other cover layer containing each ambient defect edge. Determine sharp support bounds, realizability, and induced-subtree criteria.

**Proof route:** SAT/ILP enumerate colored tensors under triangle-free constraints in each color and K4-freeness in the union.

**Falsifier:** A smallest colored tensor violating any proposed bound or failing realizability.

**Lean mission:** `layerColored_typeDefectTensor`

## XTRANS01 — Transversal-Absorbed Tree Theorem

**Status:** `CONDITIONAL_ON_738_T` · **Package:** D — Transversals · **Claim hash:** `44f596a2ac146b7e138034c494a1d80572de724c70018688a91b3ed157b93517`

Assume #738(T) with chromatic bound \(c(T)\). If \(D\) is a triangle transversal of a graph \(G\) and \(\chi(G-D)>c(T)\), then there is a vertex set \(X\) such that \((G-D)[X]\cong T\), and every ambient chord of that copy lies in \(D\).

**Proof route:** G-D is triangle-free; apply #738(T). Any edge of G[X] absent from the induced copy in G-D belongs to D.

**Falsifier:** A high-chromatic transversal residual with no defect-absorbed induced T.

**Lean mission:** `transversalResidual_contains_defectAbsorbedTree`

## XTRANS02 — Exact Tree-Absorption Dictionary

**Status:** `PROVED_IN_PACKET` · **Package:** D — Transversals · **Claim hash:** `4f006646abe494128c3591940809a66c283807e018a10ef605bfb3a6ad8a7024`

For a triangle transversal \(D\), a vertex set \(X\) induces \(T\) in \(G-D\) if and only if the designated tree edges on \(X\) avoid \(D\) and every other edge of \(G[X]\) belongs to \(D\).

**Proof route:** Unpack inducedness in the spanning edge-deleted graph.

**Falsifier:** A set X satisfying one side but not the exact edge-membership conditions.

**Lean mission:** `treeInduced_afterDeletion_iff_defects_absorbed`

## XTRANS03 — Maximal Triangle-Free / Minimal Transversal Duality

**Status:** `PROVED_IN_PACKET` · **Package:** D — Transversals · **Claim hash:** `8520810ebe9bb6dc9767e8684fe61cd4dc93640d9f42ffcb38d68f985c783858`

A spanning triangle-free subgraph \(H\subseteq G\) is maximal under edge inclusion if and only if \(E(G)\setminus E(H)\) is an inclusion-minimal triangle transversal.

**Proof route:** Adding a deleted edge to H creates a triangle exactly when removing that edge from the complement leaves some triangle unhit.

**Falsifier:** A maximal triangle-free subgraph whose complement is not minimal, or conversely.

**Lean mission:** `maximalTriangleFree_iff_minimalTriangleTransversal`

# Erdős #738 × #595 cross theorem bank — cards 11–20 of 47

**Claim boundary:** These are theorem/target cards from the 2026-08-04 #738×#595 cross-encirclement packet. `PROVED_IN_PACKET` means an explicit proof route was supplied in the packet; conditional cards retain their stated dependency; `REFUTED_ROUTE` and `UNPROVED_CHECKABLE_TARGET` are not positive theorems. Historical novelty remains unadjudicated.

## XLINK11 — Witness Link-Cover Dispersion

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `d7b194bb846b69cef699c4597c39d48416180dab63cf9628a631254f0bf494ff`

Every Erdős #595 witness has uncountable closed-neighborhood edge-cover number \(\ell(G)\), and in particular has no countable vertex cover.

**Proof route:** Contrapositive of XLINK09 and XLINK10.

**Falsifier:** A #595 witness whose edges are covered by countably many closed neighborhoods.

**Lean mission:** `erdos595_closedNeighborhoodCover_uncountable`

## XLINK12 — Localization–Dispersion Dichotomy

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `6792eb8338ca7fc47ee1037b56627210ecc1a6576524857f4767273a413ce49c`

Every Erdős #595 witness simultaneously has: (i) an uncountably chromatic triangle-free forward link under every well-order; and (ii) no countable family of closed neighborhoods covering all its edges. Thus high vertex-chromatic complexity localizes in a link, while triangle-cover complexity is necessarily dispersed across uncountably many links.

**Proof route:** Combine XLINK06 and XLINK11.

**Falsifier:** A witness failing either exact component.

**Lean mission:** `erdos595_localization_dispersion_dichotomy`

## XLINK13 — Finite Critical Link Extraction

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `a3b79bb45384f8b262a0fdede88dc8c70580a33d23ac85d4d2c226b34edeefbc`

If \(G\) is finite, \(K_4\)-free, and \(tc(G)>k\), then \(G\) contains an induced cone over a finite triangle-free vertex-critical graph \(Q\) with \(\chi(Q)>k\).

**Proof route:** Use XLINK07 to obtain a triangle-free link of chromatic number >k, then choose an induced vertex-minimal subgraph Q retaining chromatic number >k; add the apex.

**Falsifier:** A high-cover finite K4-free graph with no such critical link cone.

**Lean mission:** `finite_highCover_contains_cone_criticalTriangleFree`

## XLINK14 — Critical Bouquet Theorem

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `76daab2bb7dd4eac4be064fad4f585bf87a2575dcbb6c1a2778d5f2a9ef42a75`

Every Erdős #595 witness contains an induced subgraph
\[
K_1\vee\Bigl(\bigsqcup_{n<\omega}Q_n\Bigr),
\]
where the \(Q_n\) are pairwise anticomplete finite triangle-free vertex-critical graphs and \(\chi(Q_n)>n\).

**Proof route:** Use XLINK06 to obtain an infinite-chromatic triangle-free link H at an apex v. Choose a finite critical Q_0 of chromatic number >0. After choosing Q_n, delete its closed neighborhood inside the current triangle-free residual. The protected deletion lemma from the #738 bank preserves infinite chromatic number. Repeat. Later blocks are anticomplete to earlier blocks; add v.

**Falsifier:** A witness in which the protected recursive extraction fails at a finite stage.

**Lean mission:** `erdos595_contains_induced_criticalBouquet`

## XLINK15 — Critical Bouquet Sterility

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `f85d38be6497f4ca537dfce05432e6de2aa25d8bcb286f37c911c36ab150c652`

For any family of pairwise anticomplete triangle-free graphs \(Q_i\), the cone
\[
K_1\vee\bigsqcup_i Q_i
\]
has triangle-cover number at most \(2\), and equals \(2\) when some \(Q_i\) has an edge.

**Proof route:** Put all apex edges in one layer and all internal block edges in the other.

**Falsifier:** A cone bouquet requiring more than two triangle-free layers.

**Lean mission:** `cone_disjointTriangleFreeBlocks_triangleCover_two`

## XCONE01 — Induced Cone Lift

**Status:** `PROVED_IN_PACKET` · **Package:** B — Cone transfer · **Claim hash:** `d442503b45cd06f4df29e231d847d67b8ff43caedc97114b0f50ae57dc9b534c`

If \(F\) is an induced subgraph of \(G[N(v)]\), then \(G[\{v\}\cup V(F)]\) is the induced cone \(K_1\vee F\).

**Proof route:** The apex v is adjacent to every vertex of its neighborhood, and the edges inside F are unchanged.

**Falsifier:** An induced link copy whose apex lift has a missing apex edge or an extra internal edge.

**Lean mission:** `inducedSubgraph_link_lifts_to_cone`

## XCONE02 — χ-Bounded Cone-Transfer Principle

**Status:** `PROVED_IN_PACKET` · **Package:** B — Cone transfer · **Claim hash:** `2e4f6802ec4f6fe8fc2ddcba447f8e813895ddf76e7657c39fd51b1ded69342d`

Let \(\mathcal F\) be a family of triangle-free graphs. Suppose every triangle-free graph containing no induced member of \(\mathcal F\) has chromatic number at most \(\kappa\). Then every \(K_4\)-free graph containing no induced cone \(K_1\vee F\) with \(F\in\mathcal F\) satisfies \(tc(G)\le\kappa\).

**Proof route:** Every neighborhood is triangle-free and F-free by XCONE01; apply XLINK03.

**Falsifier:** A cone-F-free K4-free graph with tc>κ despite the assumed χ-bound.

**Lean mission:** `chiBounded_family_coneTransfer_triangleCover`

## XCONE03 — Erdős #738-to-#595 Tree-Cone Transfer

**Status:** `CONDITIONAL_ON_738_T` · **Package:** B — Cone transfer · **Claim hash:** `71d0baaf07fa2af622757d5176f20bd8160ad20958097287508d26345e87a46c`

Fix a finite tree \(T\). If every triangle-free induced-\(T\)-free graph is \(c(T)\)-colorable, then every \(K_4\)-free induced-\((K_1\vee T)\)-free graph has \(tc(G)\le c(T)\).

**Proof route:** Specialize XCONE02 to the one-element family {T}.

**Falsifier:** A verified #738 bound together with a K4-free cone-T-free graph of larger triangle-cover number.

**Lean mission:** `gyarfasSumner_triangleFree_implies_coneTriangleCoverBound`

## XCONE04 — Cone-Free High-Cover Counterexample Extractor

**Status:** `PROVED_IN_PACKET` · **Package:** B — Cone transfer · **Claim hash:** `7c533ff700a3a54891a62d20594d4631a292f565074a4264a6f02e79e87c1fbb`

If a finite \(K_4\)-free induced-\((K_1\vee T)\)-free graph has \(tc(G)>k\), then it contains a triangle-free induced-\(T\)-free neighborhood of chromatic number greater than \(k\).

**Proof route:** Use XLINK07. Cone-freeness forces every extracted neighborhood to be T-free.

**Falsifier:** A high-cover cone-T-free graph whose every link is k-colorable or contains T.

**Lean mission:** `coneFree_highCover_extracts_treeFree_highChromatic_link`

## XCONE05 — Conditional Cone Universality of #595 Witnesses

**Status:** `CONDITIONAL_ON_738_T` · **Package:** B — Cone transfer · **Claim hash:** `48ed181299d6a22347c5e58b8cfb01b2ef817c6a0b35237eeae9b0b0eb0aad72`

If the triangle-free Gyárfás–Sumner statement holds for a finite tree \(T\), then every Erdős #595 witness contains an induced \(K_1\vee T\).

**Proof route:** A witness has tc>ℵ₀, hence exceeds the finite bound c(T); apply the contrapositive of XCONE03.

**Falsifier:** A #595 witness avoiding the cone despite a verified finite #738 bound.

**Lean mission:** `erdos595_witness_contains_cone_of_tree`

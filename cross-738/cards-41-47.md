# Erdős #738 × #595 cross theorem bank — cards 41–47 of 47

**Claim boundary:** These are theorem/target cards from the 2026-08-04 #738×#595 cross-encirclement packet. `PROVED_IN_PACKET` means an explicit proof route was supplied in the packet; conditional cards retain their stated dependency; `REFUTED_ROUTE` and `UNPROVED_CHECKABLE_TARGET` are not positive theorems. Historical novelty remains unadjudicated.

## XTRANS04 — Minimal-Transversal Centeredness Suffices

**Status:** `PROVED_IN_PACKET` · **Package:** D — Transversals · **Claim hash:** `fb95ab2dd39460eae8115791123b10e9077a69736838bebf6c583c6cf19e49b2`

For a graph \(G\), \(tc(G)>\aleph_0\) if and only if every countable family of inclusion-minimal triangle transversals has nonempty intersection.

**Proof route:** One direction is immediate from centeredness of all transversals. Conversely, every transversal contains an inclusion-minimal transversal: use Zorn on descending transversals; finite triangle edge sets ensure intersections of chains remain transversals. Replace each member of an arbitrary countable family by a minimal subtransversal.

**Falsifier:** A transversal with no minimal subtransversal, or a countable minimal family violating the equivalence.

**Lean mission:** `triangleCover_gt_omega_iff_minimalTransversals_countablyCentered`

## XTRANS05 — Maximal-Layer Form of Erdős #595

**Status:** `PROVED_IN_PACKET` · **Package:** D — Transversals · **Claim hash:** `35fa37125859a724d438b1a5d3e1e9c915b0bc9033cc002092cb8a6b97325be8`

A graph has \(tc(G)>\aleph_0\) if and only if no countable family of maximal spanning triangle-free subgraphs covers \(E(G)\).

**Proof route:** Translate XTRANS04 through XTRANS03, or extend every triangle-free layer to a maximal one by Zorn.

**Falsifier:** A countable maximal-layer cover of a tc>ℵ₀ graph, or the converse.

**Lean mission:** `erdos595_iff_no_countable_maximalTriangleFreeCover`

## XTRANS06 — Tree-Rich Maximal-Layer Interface

**Status:** `CONDITIONAL_ON_738_T` · **Package:** D — Transversals · **Claim hash:** `f0bc11c9e48ed4a9d55eb2bc545118539035b33c8d3b2d43ad4d59cab1680187`

Conditional on #738(T): every maximal triangle-free spanning subgraph \(H\) of \(G\) with \(\chi(H)>c(T)\) contains an induced \(T\), whose ambient defects are exactly edges of the corresponding minimal transversal.

**Proof route:** Apply #738(T) to H and XTRANS02 to its complement.

**Falsifier:** A high-chromatic maximal layer lacking T or with a defect outside its complement.

**Lean mission:** `maximalTriangleFreeLayer_tree_and_defectTransversal`

## XMIG01 — Arbitrarily High Link Chromatic Number with \(tc=2\)

**Status:** `PROVED_IN_PACKET` · **Package:** E — Migration · **Claim hash:** `cabf6f15f6fa9e94c28187556f1c5ef00df212b7ffa1f22e23b25e21b268b5d2`

For every cardinal \(\kappa\) realized as the chromatic number of a triangle-free graph \(H\), there is a \(K_4\)-free graph \(G\) with \(tc(G)=2\) and a vertex whose neighborhood has chromatic number \(\kappa\).

**Proof route:** Take G=K1∨H and apply XCONE08.

**Falsifier:** A triangle-free H whose cone fails the stated parameters.

**Lean mission:** `highChromaticLink_coexists_triangleCover_two`

## XMIG02 — Local #738 Richness Does Not Carry #595 Complexity

**Status:** `REFUTED_ROUTE` · **Package:** E — Migration · **Claim hash:** `154d534b5ce982a4f00399d57496b604181e78f93aaa85e97ebd3529412439f1`

A \(K_4\)-free graph may contain in one link every finite configuration, critical block, contact-code pattern, or type-tensor pattern available in a triangle-free graph, while the entire graph still has triangle-cover number two.

**Proof route:** Cone the chosen triangle-free host; use XCONE08.

**Falsifier:** A proposed theorem deriving high tc solely from one link's 738 invariants.

**Lean mission:** `local738_richness_not_imply_595_complexity`

## XMIG03 — Critical-Bouquet Complexity Is Still Two-Layer

**Status:** `PROVED_IN_PACKET` · **Package:** E — Migration · **Claim hash:** `35e6be54cff508f490d1171d6063c69fb015185da7e7c67075ceccfcee065007`

The exact critical bouquet forced inside every #595 witness by XLINK14 is itself two-layer coverable. Therefore the flagship obstruction is not contained in the bouquet alone but in its interaction with the rest of the witness.

**Proof route:** Combine XLINK14 with XLINK15.

**Falsifier:** A critical bouquet whose induced subgraph itself has uncountable triangle-cover number.

**Lean mission:** `criticalBouquet_obstruction_migrates_outside`

## XMIG04 — Inter-Link Obstruction Principle

**Status:** `PROVED_IN_PACKET` · **Package:** E — Migration · **Claim hash:** `088ed7a7a6f30d90bea6cd2b8a0ed751d766f088e94e935b264f84d3c9f19f3b`

In a #595 witness, no single closed neighborhood and no countable family of closed neighborhoods carries all edges. Hence any complete proof or construction must control interactions among uncountably many vertex links.

**Proof route:** Single links have tc≤2 by XLINK08; countable link covers are ruled out by XLINK11.

**Falsifier:** A witness covered by countably many closed neighborhoods.

**Lean mission:** `erdos595_obstruction_requires_uncountablyMany_links`

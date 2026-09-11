# Erdős #738 × #595 cross theorem bank — cards 1–10 of 47

**Claim boundary:** These are theorem/target cards from the 2026-08-04 #738×#595 cross-encirclement packet. `PROVED_IN_PACKET` means an explicit proof route was supplied in the packet; conditional cards retain their stated dependency; `REFUTED_ROUTE` and `UNPROVED_CHECKABLE_TARGET` are not positive theorems. Historical novelty remains unadjudicated.

## XLINK01 — Ordered Forward-Link Coloring Theorem

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `50db7ddc38bfe249bac0c9ba4dd907ce4cd6bc2cc06a46853091ebc2ab69f9c1`

Let \(G\) be a graph and \(\prec\) a well-order of \(V(G)\). For each vertex \(v\), put
\(N_\prec^+(v)=\{w\in N(v):v\prec w\}\). If
\(\chi(G[N_\prec^+(v)])\le \kappa\) for every \(v\), then \(tc(G)\le\kappa\).

**Proof route:** Choose a proper \(\kappa\)-coloring \(\varphi_v\) of every forward neighborhood. For an edge \(vw\) with \(v\prec w\), color \(vw\) by \(\varphi_v(w)\). In a triangle \(v\prec w\prec x\), the vertices \(w,x\) are adjacent in \(G[N_\prec^+(v)]\), so \(vw\) and \(vx\) receive different colors.

**Falsifier:** A graph/order with all forward links κ-colorable but no κ-color nonmonochromatic triangle edge-coloring.

**Lean mission:** `triangleCover_le_forwardLinkChromatic`

## XLINK02 — Ordered Link Parameter Upper Bound

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `c45168c0b6a69e13ee2bb143ac604972ca87d081e8340cfcd466951c9e62b53c`

Define
\[
\lambda_\triangle(G)=\min_{\prec}\sup_{v\in V(G)}\chi(G[N_\prec^+(v)]),
\]
where the minimum ranges over well-orders of \(V(G)\). Then \(tc(G)\le\lambda_\triangle(G)\).

**Proof route:** Apply XLINK01 to every well-order and minimize.

**Falsifier:** A graph with triangle-cover number larger than the defined ordered-link parameter.

**Lean mission:** `triangleCover_le_orderedLinkParameter`

## XLINK03 — Full-Neighborhood Chromatic Bound

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `7a3b497449a607e2cd559289e751d83c06ede53f8518889c2973d9a8a2f9e0e9`

For every graph \(G\),
\[
tc(G)\le \sup_{v\in V(G)}\chi(G[N(v)]).
\]

**Proof route:** Every forward neighborhood is an induced subgraph of the full neighborhood; combine with XLINK01.

**Falsifier:** A graph whose triangle-cover number exceeds the chromatic number of every neighborhood.

**Lean mission:** `triangleCover_le_iSup_neighborhoodChromatic`

## XLINK04 — High-Cover Forward-Link Obstruction

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `83044473fe689f5b85822bfc3f4533912883f56dadbcb046fe84f25afb5211c9`

If \(tc(G)>\kappa\), then for every well-order \(\prec\) of \(V(G)\) there is a vertex \(v\) with
\[
\chi(G[N_\prec^+(v)])>\kappa.
\]

**Proof route:** Contrapositive of XLINK01.

**Falsifier:** A well-order of a \(tc>\kappa\) graph whose every forward link is κ-colorable.

**Lean mission:** `triangleCover_gt_forces_highChromatic_forwardLink`

## XLINK05 — K4-Free Links Are Triangle-Free

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `1dda15a9d87b8a3274083b3098e88d1a8ebfe44b0911cee8e63c815be4d3939e`

If \(G\) is \(K_4\)-free, then \(G[N(v)]\) is triangle-free for every vertex \(v\). The same holds for every forward link \(G[N_\prec^+(v)]\).

**Proof route:** A triangle inside \(N(v)\), together with \(v\), is a \(K_4\).

**Falsifier:** A K4-free graph with a triangle in a vertex neighborhood.

**Lean mission:** `K4free_neighborhood_triangleFree`

## XLINK06 — Erdős #595 Link Theorem

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `ef5be9b0724642cd4193437e57095abe8bea2b9a069d32650786a2d4bd3f5e29`

Every \(K_4\)-free graph \(G\) with \(tc(G)>\aleph_0\) has the following property: for every well-order of \(V(G)\), some forward neighborhood is an uncountably chromatic triangle-free induced subgraph.

**Proof route:** Combine XLINK04 with κ=ℵ₀ and XLINK05.

**Falsifier:** A #595 witness and a well-order with no uncountably chromatic forward link.

**Lean mission:** `erdos595_everyOrder_has_uncountablyChromatic_triangleFreeLink`

## XLINK07 — Finite High-Cover Link Extraction

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `a8f81d7346d1697526741e26cab25c8f07c788d941700b99637b06a8e8393870`

If \(G\) is finite, \(K_4\)-free, and \(tc(G)>k\), then some vertex \(v\) has a triangle-free neighborhood with chromatic number greater than \(k\). The neighborhood may be replaced by a forward neighborhood for any prescribed vertex order.

**Proof route:** Use XLINK04 with the prescribed order and XLINK05.

**Falsifier:** A finite K4-free graph with tc>k but every neighborhood k-colorable.

**Lean mission:** `finite_highTriangleCover_extracts_highChromatic_link`

## XLINK08 — Closed-Neighborhood Two-Layer Theorem

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `d40e6f9f3f3af7a083d353aa722edc2d0ec026d1a2bb42e04903098ff0b216d6`

For every \(K_4\)-free graph \(G\) and vertex \(v\),
\[
tc(G[N[v]])\le 2.
\]
It equals \(2\) exactly when \(G[N(v)]\) contains an edge, and is at most \(1\) otherwise.

**Proof route:** Split the closed-neighborhood edges into the star at v and the triangle-free link G[N(v)].

**Falsifier:** A K4-free closed neighborhood requiring three triangle-free layers.

**Lean mission:** `K4free_closedNeighborhood_triangleCover_le_two`

## XLINK09 — Closed-Neighborhood Edge-Cover Bound

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `621cc3e0bcfd954595518ea8a88a6c930cdeb2f8904ee60d9d26a185433559a8`

Let \(\ell(G)\) be the least cardinality of a set \(S\subseteq V(G)\) such that
\[
E(G)=\bigcup_{s\in S}E(G[N[s]]).
\]
If \(G\) is \(K_4\)-free, then \(tc(G)\le 2\ell(G)\) in cardinal arithmetic.

**Proof route:** Apply XLINK08 to each closed-neighborhood piece and union subadditivity.

**Falsifier:** A K4-free graph violating the inherited 2·ℓ layer cover.

**Lean mission:** `triangleCover_le_two_mul_closedNeighborhoodEdgeCover`

## XLINK10 — Vertex-Cover Bound for K4-Free Graphs

**Status:** `PROVED_IN_PACKET` · **Package:** A — Ordered links · **Claim hash:** `1ba5dd03998c074cc3b89673a44c65f68c09a2217eeef817a7ccbf855d3c2f21`

If \(S\) is a vertex cover of a \(K_4\)-free graph \(G\), then
\[
tc(G)\le 2|S|.
\]
Consequently, a \(K_4\)-free graph with a countable vertex cover is countably triangle-decomposable.

**Proof route:** Every edge has an endpoint s in S and therefore lies in G[N[s]]; apply XLINK09.

**Falsifier:** A K4-free graph with a vertex cover S but triangle-cover number above 2|S|.

**Lean mission:** `K4free_triangleCover_le_two_mul_vertexCover`

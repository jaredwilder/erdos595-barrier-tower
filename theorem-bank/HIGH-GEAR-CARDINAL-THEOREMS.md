# Erdős #595 — High-Gear cardinal theorem cards

**Author:** Jared Wilder  
**Source:** `HIGH-GEAR-SELF-GROWTH-ROUND-2-2026-08-04/HIGH-GEAR-THEOREM-CARDS.jsonl`  
**Parent problem:** Erdős #595 remains open.

The canonical atlas contains **40** `A_proved` rows in domain `high-gear-self`. They are two projections of **20 theorem identities**. The statements and source statuses below are preserved from that theorem-card source; this file does not upgrade them to Lean/kernel authority or settle historical novelty.

Throughout, `tc(G)` is the triangle-cover number used by the #595 program.

## 1. Vertex-Partition Compression Inequality

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(G\) be a graph, let \(\mathcal P\) be a partition of \(V(G)\), and let \(\mu\) be a cardinal for which \(|\mathcal P|\le 2^\mu\). Then
\[
 tc(G)\le \mu+\sup_{P\in\mathcal P}tc(G[P]).
\]

## 2. Massive Pairwise-Anticomplete Critical-Cone Packing

**Source status:** `UNCONDITIONAL_WITH_STANDARD_COMPACTNESS`

Let \(\theta=(2^\kappa)^+\), let \(G\) be \(K_4\)-free with \(tc(G)>\kappa\), and let \(f:\theta\to\omega\). Then \(G\) contains a pairwise anticomplete family of induced cones
\[
 K_1\vee Q_\alpha\qquad(\alpha<\theta),
\]
where every \(Q_\alpha\) is finite, triangle-free, vertex-critical, and \(\chi(Q_\alpha)>f(\alpha)\).

## 3. The \(2^\kappa\)-Complete Induced-Null Vertex Ideal

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(\kappa\) be infinite and define
\[
 \mathcal J_\kappa(G)=\{A\subseteq V(G):tc(G[A])\le\kappa\}.
\]
Then \(\mathcal J_\kappa(G)\) is downward closed and closed under unions of at most \(2^\kappa\) members.

## 4. Massive Vertex-Disjoint High-Link Cone Packing

**Source status:** `UNCONDITIONAL_TRANSFINITE`

Let \(\theta=(2^\kappa)^+\). Every \(K_4\)-free graph \(G\) with \(tc(G)>\kappa\) contains \(\theta\) pairwise vertex-disjoint induced cones
\[
 K_1\vee L_\alpha\qquad(\alpha<\theta),
\]
where every \(L_\alpha\) is triangle-free and \(\chi(L_\alpha)>\kappa\).

## 5. Closed-Neighborhood Escape Beyond \(2^\kappa\)

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(G\) be \(K_4\)-free with \(tc(G)>\kappa\), where \(\kappa\) is infinite. If \(S\subseteq V(G)\) and \(|S|\le2^\kappa\), then
\[
 tc(G-N_G[S])>\kappa.
\]

## 6. Successor-of-\(2^\kappa\) Adaptive Vertex-Null Surgery

**Source status:** `UNCONDITIONAL_TRANSFINITE`

Let \(\theta=(2^\kappa)^+\), where \(\kappa\) is infinite and \(tc(G)>\kappa\). Choose vertex sets \(A_\alpha\) adaptively for \(\alpha<\theta\), with
\[
 tc\!\left(G\!\left[A_\alpha\right]\right)\le\kappa.
\]
Then for every \(\alpha<\theta\),
\[
 tc\!\left(G-\bigcup_{\beta<\alpha}A_\beta\right)>\kappa.
\]

## 7. Complete Stable-Certificate Page Eviction

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(G\) be \(K_4\)-free with \(tc(G)>\kappa\), and let \(\{H_i:i\in I\}\) be maximal spanning triangle-free subgraphs with \(|I|\le\kappa\). Choose the common omitted edge \(xy\) supplied by T10 and put \(W_i=N_{H_i}(x)\cap N_{H_i}(y)\). Then
\[
 tc\!\left(G-\left(\{x,y\}\cup\bigcup_{i\in I}W_i\right)\right)>\kappa.
\]

## 8. Canonized High-Chromatic Link Extraction

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(G\) be \(K_4\)-free with \(tc(G)>\kappa\), and let \(\langle f_\xi:\xi<\lambda\rangle\), \(\lambda\le\kappa\), be \(\kappa\)-valued vertex maps. There are a vertex \(v\), a triangle-free induced subgraph \(L\subseteq N_G(v)\), and one common profile \(p\) such that
\[
 \chi(L)>\kappa
\]
and every vertex of \(\{v\}\cup V(L)\) has profile \(p\).

## 9. Simultaneous Unary Canonization

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(\kappa\) be infinite and \(tc(G)>\kappa\). For every family
\[
 \langle f_\xi:\xi<\lambda\rangle,\qquad \lambda\le\kappa,
\]
of vertex maps with \(|\operatorname{ran}(f_\xi)|\le\kappa\), there is \(U\subseteq V(G)\) such that \(tc(G[U])>\kappa\) and every \(f_\xi\) is constant on \(U\).

## 10. Induced-Null Vertex Deletion Persistence

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(\kappa\) be infinite. If \(tc(G)>\kappa\) and \(A\in\mathcal J_\kappa(G)\), then
\[
 tc(G-A)>\kappa.
\]

## 11. Successor-Length Adaptive Edge-Null Surgery

**Source status:** `UNCONDITIONAL_TRANSFINITE`

Let \(\kappa\) be infinite, \(tc(G)>\kappa\), and \(\langle F_\alpha:\alpha<\kappa^+\rangle\) be chosen adaptively so that \(tc((V(G),F_\alpha))\le\kappa\) at every stage. For
\[
 G_\alpha=G-\bigcup_{\beta<\alpha}F_\beta,
\]
one has \(tc(G_\alpha)>\kappa\) for every \(\alpha<\kappa^+\).

## 12. Edge-Partition Self-Similarity

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(\kappa\) be infinite and \(tc(G)>\kappa\). If
\[
 E(G)=\bigcup_{i\in I}F_i,\qquad |I|\le\kappa,
\]
then \(tc((V(G),F_i))>\kappa\) for at least one \(i\).

## 13. Canonized Pairwise-Anticomplete Critical-Cone Packing

**Source status:** `UNCONDITIONAL_WITH_STANDARD_COMPACTNESS`

Under the hypotheses of HG08 and with \(G\) \(K_4\)-free, there is one common unary profile \(p\) and a family of \((2^\kappa)^+\) pairwise anticomplete induced cones \(K_1\vee Q_\alpha\) such that every vertex of every cone has profile \(p\), and the \(Q_\alpha\)'s meet arbitrary prescribed finite chromatic thresholds.

## 14. Dual Surgery Horizons

**Source status:** `UNCONDITIONAL_COROLLARY`

For a graph with \(tc(G)>\kappa\), adaptive deletion of \(\kappa\)-null edge sets is guaranteed through every stage below \(\kappa^+\), whereas adaptive deletion of induced \(\kappa\)-null vertex sets is guaranteed through every stage below \((2^\kappa)^+\).

## 15. Canonized Page-Free Subwitness

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(G\) be \(K_4\)-free with \(tc(G)>\kappa\). Fix at most \(\kappa\) maximal spanning triangle-free layers and at most \(\kappa\) \(\kappa\)-valued unary vertex maps. Then there are:

1. a common omitted edge and its stable certificate pages for the layers;
2. an induced subgraph \(G[U]\) with \(tc(G[U])>\kappa\);

such that \(U\) avoids the two endpoints and every certificate page, while all unary maps are constant on \(U\).

## 16. Successor-of-\(2^\kappa\) Common-Book Eviction Process

**Source status:** `UNCONDITIONAL_TRANSFINITE`

Let \(\theta=(2^\kappa)^+\) and \(G\) be \(K_4\)-free with \(tc(G)>\kappa\). At every stage \(\alpha<\theta\), in the current induced residual choose at most \(\kappa\) maximal spanning triangle-free layers, form their common omitted-edge certificate support as in HG18, and delete that support. Every proper-stage residual still has triangle-cover number greater than \(\kappa\).

## 17. \(2^\kappa\)-Cell Vertex Indivisibility

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(\kappa\) be infinite and \(tc(G)>\kappa\). Every partition of \(V(G)\) into at most \(2^\kappa\) cells has a cell \(P\) satisfying
\[
 tc(G[P])>\kappa.
\]

## 18. Edge-Profile Homogeneous Link Extraction

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Under the hypotheses of HG07, if \(G\) is also \(K_4\)-free, there is a common edge-profile class \(F\) such that the spanning subgraph \(G_F=(V(G),F)\) has triangle-cover number greater than \(\kappa\), and \(G_F\) contains a triangle-free forward link of chromatic number greater than \(\kappa\).

## 19. Finite/Small Edge-Profile Canonization

**Source status:** `UNCONDITIONAL_ELEMENTARY`

Let \(tc(G)>\kappa\), where \(\kappa\) is infinite. Suppose \(\langle c_\xi:\xi<\lambda\rangle\) is a family of edge maps \(c_\xi:E(G)\to X_\xi\) whose combined profile space has cardinality at most \(\kappa\). Then some common profile class \(F\subseteq E(G)\) satisfies
\[
 tc((V(G),F))>\kappa.
\]
In particular this holds for every finite family of \(\kappa\)-valued edge colorings.

## 20. Fully Canonized Page-Free Cone Civilization

**Source status:** `UNCONDITIONAL_WITH_STANDARD_COMPACTNESS`

Under the hypotheses of HG21, the page-free common profile subwitness contains \((2^\kappa)^+\) pairwise anticomplete induced critical cones, all of whose vertices share the same unary profile and avoid the original common-book certificate support.

## Atlas accounting

The 40 raw `A_proved` rows in `high-gear-self` are duplicate projections of these 20 labels. This publication drains that atlas family at theorem-identity level; it does not change the source authority class.

## Scope firewall

These are structural consequences **inside the hypothetical-witness / large-triangle-cover regime**. They do not construct a counterexample to Erdős #595 and do not solve the parent problem. Historical novelty is not asserted here.

# Erdős #595 — cross-layer theorem recoveries from the aggregate inventory

**Author:** Jared Wilder  
**Source:** `06-ALL-THEOREM-INVENTORY.json`  
**Parent problem:** Erdős #595 remains open.

The aggregate theorem inventory preserved several exact graph-theory consequences that were not exposed by exact-name search in the reader-facing #595 theorem bank. The source statements/statuses below are preserved as recovered. They are not upgraded to Lean/kernel authority, and historical novelty is not asserted.

## 1. Stable-Book Localization–Dispersion

**Source status:** `PROVED_IN_PACKET`

Every countable attempt to cover a #595 witness by maximal triangle-free layers exposes one common stable triangle book, but that book itself has triangle-cover number two. Hence the failure of the attempted cover cannot be localized to the certificate book alone and must involve its interactions with edges outside the book.

## 2. Critical Escape with Lower-Layer Ambient Defects

**Source status:** `PROVED_IN_PACKET`

Let `H_j` be a finite `k`-critical triangle-free layer in an `m`-layer cover of `G`. For every connected `S` with `2 <= |S| < k`, `H_j` has a component `C` outside `N_{H_j}[S]` with `chi(C) >= k-|S|`, and every ambient edge of `G[C]` absent from `H_j[C]` is covered by the other `m-1` layers.

## 3. Signature Defects Carry Stable Triangle Certificates

**Source status:** `PROVED_IN_PACKET`

Under `R1-MAXCONTACT` in a `K4`-free graph, every defect edge `xy` inside a nonempty path-signature fiber belongs to the minimal transversal and has a nonempty stable certificate set `W_H(xy)`. Every path contact `p` in the shared signature is itself a certificate witness.

## 4. Stable Book as a Clean Branch Reservoir

**Source status:** `PROVED_IN_PACKET`

The page set of every common omitted-edge book in a `K4`-free graph is stable. Hence, relative to any outside finite candidate set, the #738 clean-child/large-fan dichotomy applies to any chosen neighborhood subset of that page set without internal page conflicts.

## 5. Critical Escape Defects as Lower-Layer Transversal Data

**Source status:** `PROVED_IN_PACKET`

In an `m`-layer graph, a high-chromatic critical escape component extracted inside one triangle-free layer has all ambient nonlayer edges covered by the remaining `m-1` layers; equivalently those lower layers form a triangle-free cover of the escape defect graph.

## 6. Layered Signature-Fiber Defect Descent

**Source status:** `PROVED_IN_PACKET`

Let `G` be covered by `m` triangle-free layers `H_i`. Let `P` be an induced path in `H_j` and let `F` be the vertices outside `P` having one fixed nonempty `H_j`-contact signature on `P`. Then every ambient edge of `G[F]` is covered by the other `m-1` layers, so `tc(G[F]) <= m-1`.

## 7. Finite Contact-Language Reduction for Layered Defects

**Source status:** `PROVED_IN_PACKET`

For an `n`-vertex induced path in one triangle-free layer of an `m`-layer graph, its vertices outside the path split into at most `F_{n+2}-1` nonempty contact-signature fibers, and each fiber's ambient internal defect graph has triangle-cover number at most `m-1`.

## 8. Sibling Defect Graphs Are Triangle-Free in K4-Free Hosts

**Source status:** `PROVED_IN_PACKET`

Let a rooted tree copy lie in a `K4`-free ambient graph. For every tree vertex `u`, the ambient graph induced by the selected children of `u` is triangle-free; in particular every sibling-defect graph is triangle-free, regardless of the type-tensor profile.

## 9. Countable Layer Family Produces a Shared Stable Page Space

**Source status:** `PROVED_IN_PACKET`

For every countable family of maximal triangle-free layers in a #595 witness, there is one edge `xy` such that every layer selects a nonempty subset of the same stable page space `N_G(x) intersect N_G(y)` as exact triangle certificates for omitting `xy`.

## 10. Protected Deletion Reserve Inside Every #595 Witness Link

**Source status:** `PROVED_IN_PACKET`

Let `G` be a `K4`-free graph with `tc(G)>aleph_0` and fix any well-order. In the uncountably chromatic triangle-free forward link supplied by `XLINK06`, every finite sequence of protected deletions from `N07` leaves an uncountably chromatic residual.

## 11. Cardinal Stable-Book Centeredness

**Source status:** `PROVED_IN_PACKET`

If `G` is `K4`-free and `tc(G)>kappa`, then every family of at most `kappa` maximal spanning triangle-free subgraphs has a common omitted edge `xy`, and every member supplies a nonempty stable certificate set inside `N_G(x) intersect N_G(y)`.

## 12. Transversal Absorption of Signature-Fiber Edges

**Source status:** `PROVED_IN_PACKET`

Let `D` be a triangle transversal of `G`, put `H=G-D`, and let `P` be an induced path in the triangle-free graph `H`. For every fixed nonempty `H`-contact signature `S` on `P`, every ambient edge joining two vertices in the `S`-fiber belongs to `D`.

## 13. Maximal-Layer Contact Defects Lie in the Minimal Transversal

**Source status:** `PROVED_IN_PACKET`

Let `H` be a maximal spanning triangle-free subgraph of `G` and `D=E(G)\E(H)`. For an induced path `P` in `H`, every edge internal to a fixed nonempty `H`-contact-signature fiber belongs to the inclusion-minimal triangle transversal `D`.

## 14. Root-Level versus Deep Spider-Defect Split

**Source status:** `PROVED_IN_PACKET`

For a spider induced in one layer of a `K4`-free `m`-layer graph, ambient chords among first arm vertices form a triangle-free graph, while every remaining ambient chord is covered by the other `m-1` layers.

## 15. Countable Signature-Fiber Cover Obstruction

**Source status:** `PROVED_IN_PACKET`

If `G` is `K4`-free and `tc(G)>aleph_0`, then no countable family of nonempty contact-signature fibers (taken from arbitrary spanning scaffolds and finite paths) has internal edge sets covering `E(G)`.

## 16. Stable Certification of Omitted Edges

**Source status:** `PROVED_IN_PACKET`

Let `G` be `K4`-free, `H` a maximal spanning triangle-free subgraph, and `D=E(G)\E(H)`. For every omitted edge `xy` in `D`, the set `W_H(xy)=N_H(x) intersect N_H(y)` is nonempty and is stable in `G`.

## 17. Layer-Induced Spider Defect Descent

**Source status:** `PROVED_IN_PACKET`

If a spider is induced inside one layer of an `m`-layer triangle-free edge cover, then all ambient chords on the spider vertices are covered by the other `m-1` layers.

## 18. K4-Free Ambient Signature-Fiber Collapse

**Source status:** `PROVED_IN_PACKET`

Let `G` be `K4`-free, let `H` be any spanning subgraph, and let `P` be a path in `H`. If `F` is a nonempty `H`-contact-signature fiber on `P`, then `G[F]` is triangle-free.

## 19. Single Stable Triangle Book Is Two-Layer Sterile

**Source status:** `PROVED_IN_PACKET`

Let `xy` be an edge and `W` a stable set of common neighbors of `x` and `y`. The graph on `{x,y} union W` has triangle-cover number exactly `2` when `W` is nonempty.

## Scope firewall

These are structural statements inside the #595 / `K4`-free / layered-cover architecture. They do not construct a #595 counterexample and do not solve the parent problem. Cross-program references such as `#738`, `R1-MAXCONTACT`, `XLINK06`, and `N07` retain the hypotheses encoded by their source program rather than being silently generalized here.

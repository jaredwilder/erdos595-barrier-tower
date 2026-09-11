/-
Erdos #595 — THE TRANSVERSAL DUALITY, in the source file's own vocabulary.

Packet cards T04 / T05 / T06 (blocker-centeredness duality), lowered to
`IsCountableUnionOfTriangleFree` of
oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/595.lean.

The flagship becomes a statement about a FAMILY OF SETS rather than about colourings:

  G is an Erdos #595 witness
    iff
  the family of triangle transversals of G is COUNTABLY CENTERED over E(G):
  every countable family of transversals has an edge of G in its intersection.

Self-contained; no `sorry`; `#print axioms` at the tail.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Operations

open SimpleGraph

namespace Erdos595T

variable {V : Type*}

/-- Verbatim from the source file. -/
def IsCountableUnionOfTriangleFree (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-- A triangle transversal: a set of unordered pairs meeting the edge set of every triangle
of `G`. -/
def IsTransversal (G : SimpleGraph V) (D : Set (Sym2 V)) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c →
    s(a, b) ∈ D ∨ s(a, c) ∈ D ∨ s(b, c) ∈ D

/-- A graph with no triangle in the `IsTransversal` sense is `CliqueFree 3`. -/
theorem cliqueFree_of_no_triangle (H : SimpleGraph V)
    (h : ∀ a b c : V, H.Adj a b → H.Adj a c → H.Adj b c → False) : H.CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨hcl, hcard⟩ := ht
  obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ t := by rw [hteq]; simp
  have hb : b ∈ t := by rw [hteq]; simp
  have hc : c ∈ t := by rw [hteq]; simp
  exact h a b c (hcl ha hb hab) (hcl ha hc hac) (hcl hb hc hbc)

/-- **T04 / T05, the duality.** A graph is a countable union of triangle-free graphs exactly
when countably many triangle transversals can be chosen whose intersection misses every edge. -/
theorem countableUnion_iff_transversals (G : SimpleGraph V) :
    IsCountableUnionOfTriangleFree G ↔
      ∃ D : ℕ → Set (Sym2 V), (∀ n, IsTransversal G (D n)) ∧
        ∀ e ∈ G.edgeSet, ∃ n, e ∉ D n := by
  classical
  constructor
  · rintro ⟨H, hfree, hEq⟩
    refine ⟨fun n => {e | e ∉ (H n).edgeSet}, ?_, ?_⟩
    · intro n a b c _ _ _
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2, h3⟩ := hcon
      simp only [Set.mem_setOf_eq, not_not] at h1 h2 h3
      exact hfree n {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩)
    · intro e he
      revert he
      refine Sym2.ind (fun a b he => ?_) e
      rw [mem_edgeSet, hEq, iSup_adj] at he
      obtain ⟨n, hn⟩ := he
      exact ⟨n, by simpa using hn⟩
  · rintro ⟨D, hD, hcov⟩
    refine ⟨fun n => G.deleteEdges (D n), ?_, ?_⟩
    · intro n
      refine cliqueFree_of_no_triangle _ (fun a b c h1 h2 h3 => ?_)
      rw [deleteEdges_adj] at h1 h2 h3
      rcases hD n a b c h1.1 h2.1 h3.1 with h | h | h
      · exact h1.2 h
      · exact h2.2 h
      · exact h3.2 h
    · ext a b
      rw [iSup_adj]
      constructor
      · intro hab
        obtain ⟨n, hn⟩ := hcov s(a, b) hab
        exact ⟨n, by rw [deleteEdges_adj]; exact ⟨hab, hn⟩⟩
      · rintro ⟨n, hn⟩
        rw [deleteEdges_adj] at hn
        exact hn.1

/-- **T06, the witness form.** `G` is an Erdos #595 witness exactly when its triangle
transversals are countably centered over the edge set: every countable family of transversals
has an edge of `G` common to all of them. -/
theorem witness_iff_countably_centered (G : SimpleGraph V) :
    ¬ IsCountableUnionOfTriangleFree G ↔
      ∀ D : ℕ → Set (Sym2 V), (∀ n, IsTransversal G (D n)) →
        ∃ e ∈ G.edgeSet, ∀ n, e ∈ D n := by
  rw [countableUnion_iff_transversals]
  constructor
  · intro h D hD
    by_contra hcon
    push_neg at hcon
    exact h ⟨D, hD, fun e he => hcon e he⟩
  · rintro h ⟨D, hD, hcov⟩
    obtain ⟨e, he, hall⟩ := h D hD
    obtain ⟨n, hn⟩ := hcov e he
    exact hn (hall n)

end Erdos595T

#print axioms Erdos595T.cliqueFree_of_no_triangle
#print axioms Erdos595T.countableUnion_iff_transversals
#print axioms Erdos595T.witness_iff_countably_centered

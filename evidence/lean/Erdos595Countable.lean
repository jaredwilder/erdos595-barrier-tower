/-
Erdos #595 — the COUNTABLE FLOOR, in the source file's own vocabulary.

Source: oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/595.lean
        (`IsCountableUnionOfTriangleFree`, verbatim below).

Two facts the source file does NOT carry, and every route to the flagship needs:
  T13  a graph with countably many edges IS a countable union of triangle-free graphs
       (so every #595 witness has uncountably many edges — the floor under the barrier)
  T21  the class is closed under countable unions
       (so a witness is not assembled from countably many non-witnesses)

Self-contained; no `sorry`; `#print axioms` at the tail.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Equiv.Nat

open SimpleGraph Set

namespace Erdos595C

variable {V : Type*}

/-- Verbatim from the source file. -/
def IsCountableUnionOfTriangleFree (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-- A graph whose edge set has at most one element is triangle-free. -/
theorem cliqueFree_three_of_subsingleton_edges (H : SimpleGraph V)
    (h : ∀ e₁ ∈ H.edgeSet, ∀ e₂ ∈ H.edgeSet, e₁ = e₂) : H.CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨hcl, hcard⟩ := ht
  obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ t := by rw [hteq]; simp
  have hb : b ∈ t := by rw [hteq]; simp
  have hc : c ∈ t := by rw [hteq]; simp
  have e1 : s(a, b) ∈ H.edgeSet := hcl ha hb hab
  have e2 : s(a, c) ∈ H.edgeSet := hcl ha hc hac
  have := h _ e1 _ e2
  rw [Sym2.eq_iff] at this
  rcases this with ⟨-, hbc'⟩ | ⟨h1, -⟩
  · exact hbc hbc'
  · exact hac h1

/-- **T13.** A graph with countably many edges is a countable union of triangle-free graphs:
put every edge in a layer of its own. -/
theorem countable_edges (G : SimpleGraph V) (hG : Countable G.edgeSet) :
    IsCountableUnionOfTriangleFree G := by
  classical
  obtain ⟨cc, hcc⟩ := Countable.exists_injective_nat G.edgeSet
  refine ⟨fun n => fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, cc ⟨e, h⟩ = n}, ?_, ?_⟩
  · intro n
    refine cliqueFree_three_of_subsingleton_edges _ ?_
    intro e₁ h₁ e₂ h₂
    revert h₁ h₂
    refine Sym2.ind (fun a b => ?_) e₁
    refine Sym2.ind (fun x y => ?_) e₂
    intro h₁ h₂
    rw [mem_edgeSet, fromEdgeSet_adj] at h₁ h₂
    obtain ⟨⟨hm₁, hv₁⟩, -⟩ := h₁
    obtain ⟨⟨hm₂, hv₂⟩, -⟩ := h₂
    have : (⟨s(a, b), hm₁⟩ : G.edgeSet) = ⟨s(x, y), hm₂⟩ := hcc (hv₁.trans hv₂.symm)
    exact congrArg Subtype.val this
  · ext a b
    rw [iSup_adj]
    constructor
    · intro hab
      have hm : s(a, b) ∈ G.edgeSet := hab
      exact ⟨cc ⟨s(a, b), hm⟩, by
        rw [fromEdgeSet_adj]
        exact ⟨⟨hm, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [fromEdgeSet_adj] at hn
      exact hn.1.1

/-- **T21.** The class is closed under countable unions. -/
theorem closed_countable_iSup (F : ℕ → SimpleGraph V)
    (hF : ∀ j, IsCountableUnionOfTriangleFree (F j)) :
    IsCountableUnionOfTriangleFree (⨆ j, F j) := by
  classical
  choose H hHfree hHeq using hF
  refine ⟨fun n => H (Nat.unpair n).1 (Nat.unpair n).2, fun n => hHfree _ _, ?_⟩
  ext a b
  rw [iSup_adj, iSup_adj]
  constructor
  · rintro ⟨j, hj⟩
    rw [hHeq j, iSup_adj] at hj
    obtain ⟨i, hi⟩ := hj
    exact ⟨Nat.pair j i, by simpa [Nat.unpair_pair] using hi⟩
  · rintro ⟨n, hn⟩
    exact ⟨(Nat.unpair n).1, by rw [hHeq]; exact iSup_adj.mpr ⟨(Nat.unpair n).2, hn⟩⟩

/-- **The floor.** Any Erdos #595 witness has uncountably many edges. -/
theorem witness_edges_uncountable (G : SimpleGraph V)
    (h : ¬ IsCountableUnionOfTriangleFree G) : ¬ Countable G.edgeSet :=
  fun hc => h (countable_edges G hc)

end Erdos595C

#print axioms Erdos595C.cliqueFree_three_of_subsingleton_edges
#print axioms Erdos595C.countable_edges
#print axioms Erdos595C.closed_countable_iSup
#print axioms Erdos595C.witness_edges_uncountable

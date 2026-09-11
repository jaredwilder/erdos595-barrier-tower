/-
Erdos #595 — HOMOMORPHISM PULLBACK, in the source file's own vocabulary.

Packet card T15 (and T14, subgraph monotonicity, which the source file already carries),
lowered to `IsCountableUnionOfTriangleFree` of
oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/595.lean.

The tool the construct branch lacked: the witness property travels FORWARD along graph
homomorphisms. A witness maps only into witnesses, so hunting a witness may be replaced by
hunting a graph that admits no homomorphism into any countably decomposable graph.

Self-contained; no `sorry`; `#print axioms` at the tail.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

open SimpleGraph

namespace Erdos595H

variable {V W : Type*}

/-- Verbatim from the source file. -/
def IsCountableUnionOfTriangleFree (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-- The pullback of a triangle-free graph along any map is triangle-free. -/
theorem cliqueFree_comap {f : V → W} {H : SimpleGraph W} (hH : H.CliqueFree 3) :
    (H.comap f).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨hcl, hcard⟩ := ht
  obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ t := by rw [hteq]; simp
  have hb : b ∈ t := by rw [hteq]; simp
  have hc : c ∈ t := by rw [hteq]; simp
  have e1 : H.Adj (f a) (f b) := hcl ha hb hab
  have e2 : H.Adj (f a) (f c) := hcl ha hc hac
  have e3 : H.Adj (f b) (f c) := hcl hb hc hbc
  exact hH {f a, f b, f c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨e1, e2, e3⟩)

/-- **T15.** If `G` maps homomorphically into a graph that IS a countable union of
triangle-free graphs, then `G` is one too. -/
theorem pullback_countableUnion {G : SimpleGraph V} {K : SimpleGraph W} (f : V → W)
    (hf : ∀ a b, G.Adj a b → K.Adj (f a) (f b))
    (hK : IsCountableUnionOfTriangleFree K) :
    IsCountableUnionOfTriangleFree G := by
  obtain ⟨H, hfree, hEq⟩ := hK
  refine ⟨fun i => G ⊓ (H i).comap f, fun i => ?_, ?_⟩
  · exact (cliqueFree_comap (hfree i)).anti inf_le_right
  · ext a b
    rw [iSup_adj]
    constructor
    · intro hab
      have hK : K.Adj (f a) (f b) := hf a b hab
      rw [hEq, iSup_adj] at hK
      obtain ⟨i, hi⟩ := hK
      exact ⟨i, ⟨hab, hi⟩⟩
    · rintro ⟨i, hi⟩
      exact hi.1

/-- **The construct-branch tool.** A witness maps only into witnesses: if `G` is an Erdos #595
witness and `G` maps homomorphically into `K`, then `K` is not a countable union of
triangle-free graphs either. -/
theorem witness_travels_forward {G : SimpleGraph V} {K : SimpleGraph W} (f : V → W)
    (hf : ∀ a b, G.Adj a b → K.Adj (f a) (f b))
    (hG : ¬ IsCountableUnionOfTriangleFree G) :
    ¬ IsCountableUnionOfTriangleFree K :=
  fun hK => hG (pullback_countableUnion f hf hK)

end Erdos595H

#print axioms Erdos595H.cliqueFree_comap
#print axioms Erdos595H.pullback_countableUnion
#print axioms Erdos595H.witness_travels_forward

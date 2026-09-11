/-
Erdos #595 — STABILITY OF THE WITNESS PROPERTY, in the source file's vocabulary.

Packet cards T16 (independent blow-up invariance) and T31 (triangle-inert bridges),
lowered to `IsCountableUnionOfTriangleFree` of
oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/595.lean.

Both say a construction may be reshaped without losing or gaining the property:
  T16  blowing every vertex up into a nonempty independent set changes nothing
  T31  adding edges that lie in no triangle of the result changes nothing
Together they say a witness may be assumed connected-by-bridges and vertex-blown-up,
which is what any assembly of finite obstructions needs.

Self-contained; no `sorry`; `#print axioms` at the tail.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

open SimpleGraph

namespace Erdos595S

variable {V : Type*}

/-- Verbatim from the source file. -/
def IsCountableUnionOfTriangleFree (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-- The pullback of a triangle-free graph along any map is triangle-free. -/
theorem cliqueFree_comap {W : Type*} {f : V → W} {H : SimpleGraph W} (hH : H.CliqueFree 3) :
    (H.comap f).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨hcl, hcard⟩ := ht
  obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ t := by rw [hteq]; simp
  have hb : b ∈ t := by rw [hteq]; simp
  have hc : c ∈ t := by rw [hteq]; simp
  exact hH {f a, f b, f c} (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨hcl ha hb hab, hcl ha hc hac, hcl hb hc hbc⟩)

/-- Packet card T15, restated here so this file stands alone. -/
theorem pullback_countableUnion {W : Type*} {G : SimpleGraph V} {K : SimpleGraph W} (f : V → W)
    (hf : ∀ a b, G.Adj a b → K.Adj (f a) (f b))
    (hK : IsCountableUnionOfTriangleFree K) :
    IsCountableUnionOfTriangleFree G := by
  obtain ⟨H, hfree, hEq⟩ := hK
  refine ⟨fun i => G ⊓ (H i).comap f, fun i => (cliqueFree_comap (hfree i)).anti inf_le_right, ?_⟩
  ext a b
  rw [iSup_adj]
  constructor
  · intro hab
    have hKab : K.Adj (f a) (f b) := hf a b hab
    rw [hEq, iSup_adj] at hKab
    obtain ⟨i, hi⟩ := hKab
    exact ⟨i, ⟨hab, hi⟩⟩
  · rintro ⟨i, hi⟩
    exact hi.1

/-! ### T16 — blow-up invariance -/

/-- The independent blow-up of `G` with fibres `ι v`: vertices are pairs, adjacency ignores
the fibre coordinate, so each fibre is independent and each edge becomes complete bipartite. -/
abbrev blowup (G : SimpleGraph V) (ι : V → Type*) : SimpleGraph (Σ v, ι v) :=
  G.comap Sigma.fst

/-- **T16.** A blow-up with nonempty fibres is a countable union of triangle-free graphs
exactly when the base graph is. -/
theorem blowup_countableUnion_iff (G : SimpleGraph V) (ι : V → Type*)
    (pt : ∀ v, ι v) :
    IsCountableUnionOfTriangleFree (blowup G ι) ↔ IsCountableUnionOfTriangleFree G := by
  constructor
  · intro hB
    exact pullback_countableUnion (fun v => (⟨v, pt v⟩ : Σ v, ι v)) (fun a b hab => hab) hB
  · intro hG
    exact pullback_countableUnion Sigma.fst (fun a b hab => hab) hG

/-! ### T31 — triangle-inert bridges -/

/-- **T31.** Adding edges that lie in no triangle of the result does not change the property. -/
theorem add_inert_edges (G G' : SimpleGraph V) (hle : G ≤ G')
    (hinert : ∀ a b, G'.Adj a b → ¬ G.Adj a b → ∀ c, ¬ (G'.Adj a c ∧ G'.Adj b c))
    (hG : IsCountableUnionOfTriangleFree G) :
    IsCountableUnionOfTriangleFree G' := by
  classical
  obtain ⟨H, hfree, hEq⟩ := hG
  have hHle : ∀ i, H i ≤ G := fun i => by rw [hEq]; exact le_iSup H i
  set L : SimpleGraph V := H 0 ⊔ (G' \ G) with hL
  have toG' : ∀ {x y : V}, L.Adj x y → G'.Adj x y := by
    intro x y hxy
    rcases hxy with h | h
    · exact hle (hHle 0 h)
    · exact h.1
  refine ⟨fun i => Nat.casesOn i L (fun k => H (k + 1)), ?_, ?_⟩
  · rintro (_ | k)
    · show L.CliqueFree 3
      intro t ht
      obtain ⟨hcl, hcard⟩ := ht
      obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ t := by rw [hteq]; simp
      have hb : b ∈ t := by rw [hteq]; simp
      have hc : c ∈ t := by rw [hteq]; simp
      have e1 : L.Adj a b := hcl ha hb hab
      have e2 : L.Adj a c := hcl ha hc hac
      have e3 : L.Adj b c := hcl hb hc hbc
      have g1 : G'.Adj a b := toG' e1
      have g2 : G'.Adj a c := toG' e2
      have g3 : G'.Adj b c := toG' e3
      rcases e1 with h1 | h1
      · rcases e2 with h2 | h2
        · rcases e3 with h3 | h3
          · exact hfree 0 {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩)
          · exact hinert b c h3.1 h3.2 a ⟨g1.symm, g2.symm⟩
        · exact hinert a c h2.1 h2.2 b ⟨g1, g3.symm⟩
      · exact hinert a b h1.1 h1.2 c ⟨g2, g3⟩
    · exact hfree (k + 1)
  · ext a b
    rw [iSup_adj]
    constructor
    · intro hab
      by_cases hGab : G.Adj a b
      · rw [hEq, iSup_adj] at hGab
        obtain ⟨i, hi⟩ := hGab
        rcases i with _ | k
        · exact ⟨0, Or.inl hi⟩
        · exact ⟨k + 1, hi⟩
      · exact ⟨0, Or.inr ⟨hab, hGab⟩⟩
    · rintro ⟨i, hi⟩
      rcases i with _ | k
      · exact toG' hi
      · exact hle (hHle (k + 1) hi)

end Erdos595S

#print axioms Erdos595S.blowup_countableUnion_iff
#print axioms Erdos595S.add_inert_edges

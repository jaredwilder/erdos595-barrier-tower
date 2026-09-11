/-
Erdos #595 — THE DISPERSION CRITERION, in the source file's own vocabulary.

Packet cards T38 / T39 / T40 / T41 / T43 of
oracle/evidence/erdos595/ERDOS-595-ENCIRCLEMENT-THEOREM-REFINERY-2026-08-04.md,
lowered to the predicate `IsCountableUnionOfTriangleFree` of
oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/595.lean.

This is a SUFFICIENT CONDITION for a witness, not a witness:
  every triangle-free subgraph of G is C-colourable
  AND G is not (ℕ → C)-colourable
  ⇒ G is not a countable union of triangle-free graphs.

Self-contained; no `sorry`; `#print axioms` at the tail.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Erdos595D

variable {V : Type*}

/-- Verbatim from the source file. -/
def IsCountableUnionOfTriangleFree (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-- A proper vertex colouring by an arbitrary palette. -/
def IsProper (G : SimpleGraph V) {C : Type*} (f : V → C) : Prop :=
  ∀ a b : V, G.Adj a b → f a ≠ f b

/-- **T38 / T39, the product-colouring lemma.** A countable edge cover by subgraphs each
carrying a proper `C`-colouring gives the whole graph a proper `(ℕ → C)`-colouring: colour a
vertex by its profile of colours across the layers. -/
theorem isProper_iSup_pi {C : Type*} (H : ℕ → SimpleGraph V) (f : ℕ → V → C)
    (hf : ∀ i, IsProper (H i) (f i)) :
    IsProper (⨆ i, H i) (fun v => fun i => f i v) := by
  intro a b hab hcon
  rw [iSup_adj] at hab
  obtain ⟨i, hi⟩ := hab
  exact hf i a b hi (congrFun hcon i)

/-- **T40 / T41 / T43, the dispersion criterion.** If every triangle-free subgraph of `G`
carries a proper `C`-colouring, and `G` carries no proper `(ℕ → C)`-colouring, then `G` is
not a countable union of triangle-free graphs — an Erdos #595 witness whenever `G` is also
`K₄`-free. -/
theorem not_countableUnion_of_dispersion {C : Type*} (G : SimpleGraph V)
    (htau : ∀ H : SimpleGraph V, H ≤ G → H.CliqueFree 3 → ∃ f : V → C, IsProper H f)
    (hchi : ∀ f : V → (ℕ → C), ¬ IsProper G f) :
    ¬ IsCountableUnionOfTriangleFree G := by
  classical
  rintro ⟨H, hfree, hEq⟩
  have hle : ∀ i, H i ≤ G := by
    intro i
    rw [hEq]
    exact le_iSup H i
  choose f hf using fun i => htau (H i) (hle i) (hfree i)
  refine hchi (fun v => fun i => f i v) ?_
  rw [hEq]
  exact isProper_iSup_pi H f hf

/-- The contrapositive shape actually used when hunting a witness: a `K₄`-free graph meeting
the two dispersion hypotheses IS an Erdos #595 witness. -/
theorem erdos595_witness_of_dispersion {C : Type*} (G : SimpleGraph V)
    (hK4 : G.CliqueFree 4)
    (htau : ∀ H : SimpleGraph V, H ≤ G → H.CliqueFree 3 → ∃ f : V → C, IsProper H f)
    (hchi : ∀ f : V → (ℕ → C), ¬ IsProper G f) :
    G.CliqueFree 4 ∧ ¬ IsCountableUnionOfTriangleFree G :=
  ⟨hK4, not_countableUnion_of_dispersion G htau hchi⟩

end Erdos595D

#print axioms Erdos595D.isProper_iSup_pi
#print axioms Erdos595D.not_countableUnion_of_dispersion
#print axioms Erdos595D.erdos595_witness_of_dispersion

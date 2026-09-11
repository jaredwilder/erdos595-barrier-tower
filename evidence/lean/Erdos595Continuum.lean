/-
Erdos #595 — THE CONTINUUM BARRIER.
Kernel seal of T10/T11/T12 of the refinery packet
`oracle/evidence/erdos595/ERDOS-595-ENCIRCLEMENT-THEOREM-REFINERY-2026-08-04.md`
(claim hashes 268c7cd2 / 8d1956bf / fe1ccc2b).

Route, taken from the packet itself: T07 (bipartite cover number = least kappa with
chi <= 2^kappa) composed with T09 (tc <= bc) collapses into ONE argument once the
vertex colours are coded as binary kappa-sequences: colour each edge by a coordinate
on which its endpoints' codes differ; a monochromatic triangle would need three
pairwise distinct Booleans.

Self-contained; no `sorry`; `#print axioms` at the tail.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Embedding.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic

universe u v

open scoped Classical

namespace Erdos595

variable {V : Type u} {ι : Type v}

/-- Packet T03 formulation of a triangle-free edge cover indexed by `ι`:
a colour for every unordered pair such that no triangle of `G` is monochromatic. -/
def IsTriangleFreeCover (G : SimpleGraph V) (c : Sym2 V → ι) : Prop :=
  ∀ a b d : V, G.Adj a b → G.Adj b d → G.Adj a d →
    ¬ (c s(a, b) = c s(b, d) ∧ c s(b, d) = c s(a, d))

/-- A proper vertex colouring by an arbitrary palette. -/
def IsProper (G : SimpleGraph V) {C : Type*} (f : V → C) : Prop :=
  ∀ a b : V, G.Adj a b → f a ≠ f b

/-- "The endpoints of this unordered pair differ at coordinate `i`" — symmetric by
construction, which is what makes the colour a function of the EDGE. -/
def Diff (f : V → ι → Bool) (i : ι) : Sym2 V → Prop :=
  Sym2.lift ⟨fun a b => f a i ≠ f b i, by intro a b; simp [ne_comm]⟩

@[simp] lemma Diff_mk (f : V → ι → Bool) (i : ι) (a b : V) :
    Diff f i s(a, b) ↔ f a i ≠ f b i := Iff.rfl

/-- The edge colour: a coordinate witnessing that the endpoints' codes differ. -/
noncomputable def pick [Nonempty ι] (f : V → ι → Bool) (e : Sym2 V) : ι :=
  if h : ∃ i, Diff f i e then h.choose else Classical.arbitrary ι

lemma pick_spec [Nonempty ι] (f : V → ι → Bool) {a b : V} (h : f a ≠ f b) :
    f a (pick f s(a, b)) ≠ f b (pick f s(a, b)) := by
  have hex : ∃ i, Diff f i s(a, b) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact ⟨i, hi⟩
  have hp : pick f s(a, b) = hex.choose := dif_pos hex
  rw [hp]
  exact hex.choose_spec

/-- **T10.** A proper colouring coded by binary `ι`-sequences yields a triangle-free
edge cover indexed by `ι`. -/
theorem cover_of_binaryColouring [Nonempty ι] (G : SimpleGraph V)
    (f : V → ι → Bool) (hf : IsProper G f) :
    IsTriangleFreeCover G (pick f) := by
  rintro a b d hab hbd had ⟨h1, h2⟩
  have p1 : f a (pick f s(a, b)) ≠ f b (pick f s(a, b)) := pick_spec f (hf a b hab)
  have q2 : f b (pick f s(b, d)) ≠ f d (pick f s(b, d)) := pick_spec f (hf b d hbd)
  have q3 : f a (pick f s(a, d)) ≠ f d (pick f s(a, d)) := pick_spec f (hf a d had)
  rw [← h1] at q2
  rw [← h1.trans h2] at q3
  revert p1 q2 q3
  cases f a (pick f s(a, b)) <;> cases f b (pick f s(a, b)) <;>
    cases f d (pick f s(a, b)) <;> simp

/-- **T11.** Contrapositive: no `ι`-indexed triangle-free cover forces the chromatic
number above `2 ^ #ι`. -/
theorem no_binaryColouring_of_no_cover [Nonempty ι] (G : SimpleGraph V)
    (h : ¬ ∃ c : Sym2 V → ι, IsTriangleFreeCover G c) :
    ¬ ∃ f : V → ι → Bool, IsProper G f := by
  rintro ⟨f, hf⟩
  exact h ⟨pick f, cover_of_binaryColouring G f hf⟩

/-- **T12 — the continuum barrier.** A graph that is not the union of countably many
triangle-free edge sets admits no proper colouring by any palette that embeds in the
continuum: `chi(G) > 2 ^ aleph0`. -/
theorem erdos595_witness_above_continuum (G : SimpleGraph V)
    (h : ¬ ∃ c : Sym2 V → ℕ, IsTriangleFreeCover G c) :
    ∀ (C : Type u) (e : C ↪ (ℕ → Bool)) (f : V → C), ¬ IsProper G f := by
  intro C e f hf
  refine no_binaryColouring_of_no_cover G h ⟨fun v => e (f v), ?_⟩
  intro a b hab hcon
  exact hf a b hab (e.injective hcon)

/-- **T12, vertex half.** The same hypothesis forces `#V > 2 ^ aleph0`. -/
theorem erdos595_vertices_above_continuum (G : SimpleGraph V)
    (h : ¬ ∃ c : Sym2 V → ℕ, IsTriangleFreeCover G c) :
    IsEmpty (V ↪ (ℕ → Bool)) := by
  refine ⟨fun e => ?_⟩
  exact erdos595_witness_above_continuum G h V e id (fun a b hab => G.ne_of_adj hab)


/-! ### The cardinal form: the index TYPE becomes a CARDINAL. -/

open Cardinal in
/-- **T10, cardinal form.** If `#C ≤ 2 ^ κ` for a nonzero cardinal `κ` and `G` has a proper
colouring valued in `C`, then `E(G)` is covered by `κ` triangle-free layers. -/
theorem cover_of_chromatic_le_two_pow {C : Type u} (G : SimpleGraph V) (κ : Cardinal.{u})
    (hκ : κ ≠ 0) (f : V → C) (hf : IsProper G f) (hc : #C ≤ 2 ^ κ) :
    ∃ (ι : Type u) (_ : #ι = κ) (c : Sym2 V → ι), IsTriangleFreeCover G c := by
  have hpow : #(κ.out → Bool) = 2 ^ κ := by
    simp [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_out]
  have hemb : Nonempty (C ↪ (κ.out → Bool)) := by
    rw [← Cardinal.le_def, hpow]; exact hc
  obtain ⟨e⟩ := hemb
  have hne : Nonempty κ.out := by
    rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_out]; exact hκ
  refine ⟨κ.out, Cardinal.mk_out κ, pick (fun v => e (f v)), ?_⟩
  exact cover_of_binaryColouring G (fun v => e (f v))
    (fun a b hab hcon => hf a b hab (e.injective hcon))

open Cardinal in
/-- **T11, cardinal form.** No `κ`-indexed triangle-free cover forces `χ(G) > 2 ^ κ`. -/
theorem chromatic_gt_two_pow_of_no_cover (G : SimpleGraph V) (κ : Cardinal.{u}) (hκ : κ ≠ 0)
    (h : ∀ (ι : Type u), #ι = κ → ¬ ∃ c : Sym2 V → ι, IsTriangleFreeCover G c)
    {C : Type u} (f : V → C) (hf : IsProper G f) : ¬ #C ≤ 2 ^ κ := by
  intro hc
  obtain ⟨ι, hι, c, hcov⟩ := cover_of_chromatic_le_two_pow G κ hκ f hf hc
  exact h ι hι ⟨c, hcov⟩

/-! ### The edge-cardinality clause of packet card T12. -/

/-- `(ℕ → Bool) × Bool` embeds in `ℕ → Bool`: prepend the Boolean at index `0`. -/
def prependEmb : ((ℕ → Bool) × Bool) ↪ (ℕ → Bool) where
  toFun := fun p n => Nat.casesOn n p.2 (fun k => p.1 k)
  inj' := by
    rintro ⟨f, b⟩ ⟨g, c⟩ h
    have h0 : b = c := congrFun h 0
    have hs : ∀ k, f k = g k := fun k => congrFun h (k + 1)
    simp_all [funext hs]

/-- Every vertex of a graph without isolated vertices is recoverable from a chosen
incident edge together with one bit. -/
theorem vertex_emb_edge_bool (G : SimpleGraph V) (hiso : ∀ v : V, ∃ w, G.Adj v w) :
    Nonempty (V ↪ G.edgeSet × Bool) := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder (WellOrderingRel (α := V))
  choose w hw using hiso
  refine ⟨⟨fun v => (⟨s(v, w v), by simpa using hw v⟩, decide (v ≤ w v)), ?_⟩⟩
  intro u v huv
  by_contra hne
  have he : s(u, w u) = s(v, w v) := congrArg Subtype.val (congrArg Prod.fst huv)
  have hb : decide (u ≤ w u) = decide (v ≤ w v) := congrArg Prod.snd huv
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne h1
  · subst h1
    rw [h2] at hb
    have hd := (decide_eq_decide).mp hb
    rcases le_total (w v) v with hle | hle
    · exact hne (le_antisymm hle (hd.mp hle))
    · exact hne (le_antisymm (hd.mpr hle) hle)

/-- **T12, edge half.** A graph with no isolated vertices that is not a union of countably
many triangle-free edge sets has more than continuum many edges. -/
theorem erdos595_edges_above_continuum (G : SimpleGraph V)
    (hiso : ∀ v : V, ∃ w, G.Adj v w)
    (h : ¬ ∃ c : Sym2 V → ℕ, IsTriangleFreeCover G c) :
    IsEmpty (G.edgeSet ↪ (ℕ → Bool)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨ve⟩ := vertex_emb_edge_bool G hiso
  exact (erdos595_vertices_above_continuum G h).elim
    (ve.trans ((e.prodMap (Function.Embedding.refl Bool)).trans prependEmb))

end Erdos595

#print axioms Erdos595.cover_of_binaryColouring
#print axioms Erdos595.no_binaryColouring_of_no_cover
#print axioms Erdos595.erdos595_witness_above_continuum
#print axioms Erdos595.erdos595_vertices_above_continuum
#print axioms Erdos595.cover_of_chromatic_le_two_pow
#print axioms Erdos595.chromatic_gt_two_pow_of_no_cover
#print axioms Erdos595.erdos595_edges_above_continuum

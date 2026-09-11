import Mathlib

/-!
# Erdos Problem 595 - the sealed structure library

Every statement below is written against the predicate `IsCUTF`, transcribed VERBATIM from
`FormalConjectures/ErdosProblems/595.lean` (DeepMind formal-conjectures), so the library speaks
the target's own vocabulary.

**The flagship - is there an infinite K4-free graph that is NOT a countable union of triangle-free
graphs - is OPEN and nothing here closes it.** These are bounds, barriers and reformulations.
-/

open SimpleGraph Set

namespace Erdos595Lib

/-- Verbatim from the source file. -/
def IsCUTF {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-- The same, with an arbitrary index type. -/
def IsUTF {V : Type} (I : Type) (G : SimpleGraph V) : Prop :=
  ∃ H : I → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

def IsProperC {V : Type} (G : SimpleGraph V) {C : Type} (f : V → C) : Prop :=
  ∀ a b : V, G.Adj a b → f a ≠ f b

def IsProperN {V : Type} (H : SimpleGraph V) (f : V → ℕ) : Prop :=
  ∀ a b : V, H.Adj a b → f a ≠ f b

def GoodOn {V : Type} (G : SimpleGraph V) (k : ℕ) (S : Set V) (f : Sym2 V → Fin k) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, G.Adj a b → G.Adj a c → G.Adj b c →
    ¬ (f s(a, b) = f s(a, c) ∧ f s(a, c) = f s(b, c))

/-- The link of an edge: the apexes completing it to a triangle. -/
def Link {V : Type} (G : SimpleGraph V) (a b : V) : Set V := {v | G.Adj a v ∧ G.Adj b v}

def IsProperEdgeColouring {V : Type} (G : SimpleGraph V) (c : Sym2 V → ℕ) : Prop :=
  ∀ a b d : V, G.Adj a b → G.Adj a d → b ≠ d → c s(a, b) ≠ c s(a, d)

def IsCUB {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, ∃ f : V → Bool, IsProperC (H i) f) ∧ G = ⨆ i, H i



def IsProperI {V I : Type} (H : SimpleGraph V) (f : V → I) : Prop :=
  ∀ a b : V, H.Adj a b → f a ≠ f b

def IsTransversal {V : Type} (G : SimpleGraph V) (D : Set (Sym2 V)) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c →
    s(a, b) ∈ D ∨ s(a, c) ∈ D ∨ s(b, c) ∈ D

theorem cliqueFreeSubsingleton {V : Type} (H : SimpleGraph V)
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
  have hEq := h _ e1 _ e2
  rw [Sym2.eq_iff] at hEq
  rcases hEq with ⟨-, hbc'⟩ | ⟨h1, -⟩
  · exact hbc hbc'
  · exact hac h1

theorem countableEdgesCUTF {V : Type} (G : SimpleGraph V) (hG : Countable G.edgeSet) :
    IsCUTF G := by
  classical
  obtain ⟨cc, hcc⟩ := Countable.exists_injective_nat G.edgeSet
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, cc ⟨e, h⟩ = n}, ?_, ?_⟩
  · intro n
    refine cliqueFreeSubsingleton _ ?_
    intro e₁ h₁ e₂ h₂
    revert h₁ h₂
    refine Sym2.ind (fun a b => ?_) e₁
    refine Sym2.ind (fun x y => ?_) e₂
    intro h₁ h₂
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromEdgeSet_adj] at h₁ h₂
    obtain ⟨⟨hm₁, hv₁⟩, -⟩ := h₁
    obtain ⟨⟨hm₂, hv₂⟩, -⟩ := h₂
    exact congrArg Subtype.val (hcc (hv₁.trans hv₂.symm))
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      have hm : s(a, b) ∈ G.edgeSet := hab
      exact ⟨cc ⟨s(a, b), hm⟩, by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hm, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem erdos595_compactness_T26 {V : Type} (G : SimpleGraph V) (k : ℕ) (h : ∀ S : Finset V, ∃ f : Sym2 V → Fin k, GoodOn G k (S : Set V) f) :
    ∃ f : Sym2 V → Fin k, GoodOn G k Set.univ f := by
  classical
  letI : TopologicalSpace (Fin k) := ⊥
  haveI : DiscreteTopology (Fin k) := ⟨rfl⟩
  haveI : CompactSpace (Fin k) := Finite.compactSpace
  haveI : CompactSpace (Sym2 V → Fin k) := Pi.compactSpace
  let T := {p : V × V × V // G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2}
  let C : T → Set (Sym2 V → Fin k) := fun t =>
    {f | ¬ (f s(t.1.1, t.1.2.1) = f s(t.1.1, t.1.2.2) ∧
            f s(t.1.1, t.1.2.2) = f s(t.1.2.1, t.1.2.2))}
  have hclosed : ∀ t : T, IsClosed (C t) := by
    intro t
    have hcont : Continuous (fun f : Sym2 V → Fin k =>
        (f s(t.1.1, t.1.2.1), f s(t.1.1, t.1.2.2), f s(t.1.2.1, t.1.2.2))) :=
      by fun_prop
    have heq : C t = (fun f : Sym2 V → Fin k =>
        (f s(t.1.1, t.1.2.1), f s(t.1.1, t.1.2.2), f s(t.1.2.1, t.1.2.2))) ⁻¹'
        {p : Fin k × Fin k × Fin k | ¬ (p.1 = p.2.1 ∧ p.2.1 = p.2.2)} := rfl
    rw [heq]
    exact (isClosed_discrete _).preimage hcont
  have hne : (⋂ t : T, C t).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    obtain ⟨u, hu⟩ := (isCompact_univ (X := Sym2 V → Fin k)).elim_finite_subfamily_closed
      C hclosed (by rw [Set.univ_inter, hcon])
    let S : Finset V := u.biUnion (fun t => {t.1.1, t.1.2.1, t.1.2.2})
    obtain ⟨f, hf⟩ := h S
    have hmem : f ∈ ⋂ t ∈ u, C t := by
      refine Set.mem_iInter₂.2 (fun t ht => ?_)
      have h1 : t.1.1 ∈ S := Finset.mem_biUnion.2 ⟨t, ht, by simp⟩
      have h2 : t.1.2.1 ∈ S := Finset.mem_biUnion.2 ⟨t, ht, by simp⟩
      have h3 : t.1.2.2 ∈ S := Finset.mem_biUnion.2 ⟨t, ht, by simp⟩
      exact hf _ h1 _ h2 _ h3 t.2.1 t.2.2.1 t.2.2.2
    have hmem2 : f ∈ (Set.univ : Set (Sym2 V → Fin k)) ∩ ⋂ t ∈ u, C t := ⟨trivial, hmem⟩
    rw [hu] at hmem2
    exact hmem2.elim
  obtain ⟨f, hf⟩ := hne
  refine ⟨f, ?_⟩
  intro a _ b _ c _ hab hac hbc
  exact (Set.mem_iInter.1 hf ⟨(a, b, c), ⟨hab, hac, hbc⟩⟩)

theorem erdos595_finite_obstruction_T27 {V : Type} (G : SimpleGraph V) (k : ℕ) :
    ¬ IsCUTF G → ∃ S : Finset V, ∀ f : Sym2 V → Fin k, ¬ GoodOn G k (S : Set V) f := by
  classical
  intro hw
  by_contra hcon
  push_neg at hcon
  obtain ⟨f, hf⟩ := erdos595_compactness_T26 G k (fun S => (hcon S).imp (fun g hg => hg))
  refine hw ⟨fun n => if hn : n < k then
      SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ f e = ⟨n, hn⟩} else ⊥, ?_, ?_⟩
  · intro n
    by_cases hn : n < k
    · simp only [dif_pos hn]
      intro t ht
      obtain ⟨hcl, hcard⟩ := ht
      obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ t := by rw [hteq]; simp
      have hb : b ∈ t := by rw [hteq]; simp
      have hc : c ∈ t := by rw [hteq]; simp
      have e1 := hcl ha hb hab
      have e2 := hcl ha hc hac
      have e3 := hcl hb hc hbc
      rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
      exact hf a (Set.mem_univ a) b (Set.mem_univ b) c (Set.mem_univ c)
        e1.1.1 e2.1.1 e3.1.1 ⟨by rw [e1.1.2, e2.1.2], by rw [e2.1.2, e3.1.2]⟩
    · simp only [dif_neg hn]
      exact SimpleGraph.cliqueFree_bot (by norm_num)
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      refine ⟨(f s(a, b)).1, ?_⟩
      simp only [dif_pos (f s(a, b)).2]
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨hab, by simp⟩, G.ne_of_adj hab⟩
    · rintro ⟨n, hn⟩
      by_cases hk : n < k
      · rw [dif_pos hk, SimpleGraph.fromEdgeSet_adj] at hn
        exact hn.1.1
      · rw [dif_neg hk] at hn
        exact absurd hn (by simp)

theorem erdos595_countable_core_T28 {V : Type} (G : SimpleGraph V) (hw : ¬ IsCUTF G) :
    ∃ W : Set V, W.Countable ∧ ∀ k : ℕ, ∃ S : Finset V, (S : Set V) ⊆ W ∧ ∀ f : Sym2 V → Fin k, ¬ GoodOn G k (S : Set V) f := by
  classical
  choose S hS using fun k => erdos595_finite_obstruction_T27 G k hw
  refine ⟨⋃ k : ℕ, (S k : Set V), Set.countable_iUnion (fun k => (S k).countable_toSet), ?_⟩
  intro k
  exact ⟨S k, Set.subset_iUnion (fun k => ((S k : Finset V) : Set V)) k, hS k⟩

theorem erdos595_countable_blindness {V : Type} (G : SimpleGraph V) :
    ∀ W : Set V, W.Countable → IsCUTF (G.induce W) := by
  classical
  intro W hW
  have hsub : Countable ((G.induce W).edgeSet) := by
    haveI : Countable W := hW.to_subtype
    haveI : Countable (Sym2 W) := inferInstance
    exact Subtype.countable
  exact countableEdgesCUTF _ hsub

theorem erdos595_bipartite_level_down {V : Type} (G : SimpleGraph V) :
    IsCUB G ↔ ∃ f : V → (ℕ → Bool), IsProperC G f := by
  constructor
  · rintro ⟨H, hbip, hEq⟩
    choose f hf using hbip
    refine ⟨fun v => fun i => f i v, ?_⟩
    intro a b hab hcon
    rw [hEq, SimpleGraph.iSup_adj] at hab
    obtain ⟨i, hi⟩ := hab
    exact hf i a b hi (congrFun hcon i)
  · rintro ⟨g, hg⟩
    refine ⟨fun i => SimpleGraph.fromRel (fun a b => G.Adj a b ∧ g a i ≠ g b i), ?_, ?_⟩
    · intro i
      refine ⟨fun v => g v i, ?_⟩
      intro a b hab
      rw [SimpleGraph.fromRel_adj] at hab
      rcases hab.2 with h | h
      · exact h.2
      · exact fun hc => h.2 hc.symm
    · ext a b
      rw [SimpleGraph.iSup_adj]
      constructor
      · intro hab
        obtain ⟨i, hi⟩ := Function.ne_iff.mp (hg a b hab)
        exact ⟨i, by rw [SimpleGraph.fromRel_adj]; exact ⟨G.ne_of_adj hab, Or.inl ⟨hab, hi⟩⟩⟩
      · rintro ⟨i, hi⟩
        rw [SimpleGraph.fromRel_adj] at hi
        rcases hi.2 with h | h
        · exact h.1
        · exact h.1.symm

theorem erdos595_arrow_form {V : Type} (G : SimpleGraph V) :
    ¬ IsCUTF G ↔ ∀ f : Sym2 V → ℕ, ∃ a b c : V, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ f s(a, b) = f s(a, c) ∧ f s(a, c) = f s(b, c) := by
  classical
  constructor
  · intro hw f
    by_contra hcon
    push_neg at hcon
    refine hw ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ f e = n}, ?_, ?_⟩
    · intro n t ht
      obtain ⟨hcl, hcard⟩ := ht
      obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ t := by rw [hteq]; simp
      have hb : b ∈ t := by rw [hteq]; simp
      have hc : c ∈ t := by rw [hteq]; simp
      have e1 := hcl ha hb hab
      have e2 := hcl ha hc hac
      have e3 := hcl hb hc hbc
      rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
      exact hcon a b c e1.1.1 e2.1.1 e3.1.1 (by rw [e1.1.2, e2.1.2]) (by rw [e2.1.2, e3.1.2])
    · ext a b
      rw [SimpleGraph.iSup_adj]
      constructor
      · intro hab
        exact ⟨f s(a, b), by
          rw [SimpleGraph.fromEdgeSet_adj]
          exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
      · rintro ⟨n, hn⟩
        rw [SimpleGraph.fromEdgeSet_adj] at hn
        exact hn.1.1
  · rintro harr ⟨H, hfree, hEq⟩
    have hex : ∀ e : Sym2 V, ∃ n : ℕ, e ∈ G.edgeSet → e ∈ (H n).edgeSet := by
      intro e
      by_cases he : e ∈ G.edgeSet
      · revert he
        refine Sym2.ind (fun a b he => ?_) e
        rw [SimpleGraph.mem_edgeSet, hEq, SimpleGraph.iSup_adj] at he
        obtain ⟨n, hn⟩ := he
        exact ⟨n, fun _ => hn⟩
      · exact ⟨0, fun hc => absurd hc he⟩
    obtain ⟨a, b, c, hab, hac, hbc, h1, h2⟩ :=
      harr (fun e => Nat.find (hex e))
    have m1 : s(a, b) ∈ (H (Nat.find (hex s(a, b)))).edgeSet := Nat.find_spec (hex s(a, b)) hab
    have m2 : s(a, c) ∈ (H (Nat.find (hex s(a, c)))).edgeSet := Nat.find_spec (hex s(a, c)) hac
    have m3 : s(b, c) ∈ (H (Nat.find (hex s(b, c)))).edgeSet := Nat.find_spec (hex s(b, c)) hbc
    rw [← h1] at m2
    rw [← h2, ← h1] at m3
    exact hfree (Nat.find (hex s(a, b))) {a, b, c}
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨m1, m2, m3⟩)

theorem erdos595_proper_edge_colouring {V : Type} (G : SimpleGraph V) :
    (∃ c : Sym2 V → ℕ, IsProperEdgeColouring G c) → IsCUTF G := by
  classical
  rintro ⟨c, hc⟩
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2
    exact hc a b d e1.1.1 e2.1.1 hbd (by rw [e1.1.2, e2.1.2])
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem erdos595_neighbourhood_bound {V : Type} (G : SimpleGraph V) :
    (∀ u : V, ∃ g : V → ℕ, ∀ a b : V, G.Adj u a → G.Adj u b → G.Adj a b → g a ≠ g b) → IsCUTF G := by
  classical
  intro hnb
  choose g hg using hnb
  letI : LinearOrder V := IsWellOrder.linearOrder (WellOrderingRel (α := V))
  set F : V → V → ℕ := fun a b => if a ≤ b then g a b else g b a with hF
  have hsymm : ∀ a b : V, F a b = F b a := by
    intro a b
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · rcases le_total a b with h | h
      · have h2 : ¬ b ≤ a := fun hc => hne (le_antisymm h hc)
        simp [hF, h, h2]
      · have h2 : ¬ a ≤ b := fun hc => hne (le_antisymm hc h)
        simp [hF, h, h2]
  set c : Sym2 V → ℕ := Sym2.lift ⟨F, hsymm⟩ with hc
  have hcval : ∀ a b : V, c s(a, b) = F a b := by intro a b; rfl
  have key : ∀ u x y : V, u ≤ x → u ≤ y → G.Adj u x → G.Adj u y → G.Adj x y →
      c s(u, x) = c s(u, y) → False := by
    intro u x y hux huy h1 h2 h3 heq
    rw [hcval, hcval, hF] at heq
    simp only [if_pos hux, if_pos huy] at heq
    exact hg u x y h1 h2 h3 heq
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    have g1 : G.Adj a b := e1.1.1
    have g2 : G.Adj a d := e2.1.1
    have g3 : G.Adj b d := e3.1.1
    have c1 : c s(a, b) = n := e1.1.2
    have c2 : c s(a, d) = n := e2.1.2
    have c3 : c s(b, d) = n := e3.1.2
    have swapDA : s(d, a) = s(a, d) := Sym2.eq_swap
    have swapDB : s(d, b) = s(b, d) := Sym2.eq_swap
    have swapBA : s(b, a) = s(a, b) := Sym2.eq_swap
    have kmin_a : a ≤ b → a ≤ d → False := fun h1' h2' =>
      key a b d h1' h2' g1 g2 g3 (by rw [c1, c2])
    have kmin_b : b ≤ a → b ≤ d → False := fun h1' h2' =>
      key b a d h1' h2' g1.symm g3 g2 (by rw [swapBA, c1, c3])
    have kmin_d : d ≤ a → d ≤ b → False := fun h1' h2' =>
      key d a b h1' h2' g2.symm g3.symm g1 (by rw [swapDA, swapDB, c2, c3])
    rcases le_total a b with hab' | hab'
    · rcases le_total a d with had' | had'
      · exact kmin_a hab' had'
      · exact kmin_d had' (le_trans had' hab')
    · rcases le_total b d with hbd' | hbd'
      · exact kmin_b hab' hbd'
      · exact kmin_d (le_trans hbd' hab') hbd'
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem erdos595_tc_le_tau {V : Type} (G : SimpleGraph V) :
    G.CliqueFree 4 → (∀ H : SimpleGraph V, H ≤ G → H.CliqueFree 3 → ∃ f : V → ℕ, IsProperN H f) → IsCUTF G := by
  classical
  intro hK4 htau
  refine erdos595_neighbourhood_bound G (fun u => ?_)
  set Hu : SimpleGraph V :=
    G ⊓ SimpleGraph.fromRel (fun a b => G.Adj u a ∧ G.Adj u b) with hHu
  have hle : Hu ≤ G := inf_le_left
  have hadj : ∀ a b : V, Hu.Adj a b → G.Adj a b ∧ G.Adj u a ∧ G.Adj u b := by
    intro a b h
    rw [hHu, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj] at h
    refine ⟨h.1, ?_⟩
    rcases h.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h1⟩
  have hmk : ∀ a b : V, G.Adj a b → G.Adj u a → G.Adj u b → Hu.Adj a b := by
    intro a b h1 h2 h3
    rw [hHu, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
    exact ⟨h1, G.ne_of_adj h1, Or.inl ⟨h2, h3⟩⟩
  have hfree : Hu.CliqueFree 3 := by
    intro t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    obtain ⟨g1, hua, hub⟩ := hadj a b (hcl ha hb hab)
    obtain ⟨g2, -, hud⟩ := hadj a d (hcl ha hd had)
    obtain ⟨g3, -, -⟩ := hadj b d (hcl hb hd hbd)
    have h3c : G.IsNClique 3 {a, b, d} :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨g1, g2, g3⟩
    refine hK4 (insert u {a, b, d}) (h3c.insert ?_)
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hua
    · exact hub
    · exact hud
  obtain ⟨f, hf⟩ := htau Hu hle hfree
  exact ⟨f, fun a b hua hub hab => hf a b (hmk a b hab hua hub)⟩

theorem erdos595_chi_le_two_pow_tau {V : Type} (G : SimpleGraph V) :
    G.CliqueFree 4 → (∀ H : SimpleGraph V, H ≤ G → H.CliqueFree 3 → ∃ f : V → ℕ, IsProperN H f) → ∃ F : V → (ℕ → ℕ), ∀ a b : V, G.Adj a b → F a ≠ F b := by
  classical
  intro hK4 htau
  obtain ⟨H, hfree, hEq⟩ := erdos595_tc_le_tau G hK4 htau
  choose f hf using fun i => htau (G ⊓ H i) inf_le_left ((hfree i).anti inf_le_right)
  refine ⟨fun v => fun i => f i v, ?_⟩
  intro a b hab hcon
  have hab' := hab
  rw [hEq, SimpleGraph.iSup_adj] at hab'
  obtain ⟨i, hi⟩ := hab'
  exact hf i a b ⟨hab, hi⟩ (congrFun hcon i)

theorem erdos595_upper_neighbourhood_bound {V : Type} [LinearOrder V] (G : SimpleGraph V) :
    (∀ u : V, ∃ g : V → ℕ, ∀ a b : V, u < a → u < b → G.Adj u a → G.Adj u b → G.Adj a b → g a ≠ g b) → IsCUTF G := by
  classical
  intro hnb
  choose g hg using hnb
  set F : V → V → ℕ := fun a b => if a ≤ b then g a b else g b a with hF
  have hsymm : ∀ a b : V, F a b = F b a := by
    intro a b
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · rcases le_total a b with h | h
      · have h2 : ¬ b ≤ a := fun hc => hne (le_antisymm h hc)
        simp [hF, h, h2]
      · have h2 : ¬ a ≤ b := fun hc => hne (le_antisymm hc h)
        simp [hF, h, h2]
  set c : Sym2 V → ℕ := Sym2.lift ⟨F, hsymm⟩ with hc
  have hcval : ∀ a b : V, c s(a, b) = F a b := by intro a b; rfl
  have key : ∀ u x y : V, u ≤ x → u ≤ y → G.Adj u x → G.Adj u y → G.Adj x y →
      c s(u, x) = c s(u, y) → False := by
    intro u x y hux huy h1 h2 h3 heq
    rw [hcval, hcval, hF] at heq
    simp only [if_pos hux, if_pos huy] at heq
    have hlx : u < x := lt_of_le_of_ne hux (G.ne_of_adj h1)
    have hly : u < y := lt_of_le_of_ne huy (G.ne_of_adj h2)
    exact hg u x y hlx hly h1 h2 h3 heq
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    have g1 : G.Adj a b := e1.1.1
    have g2 : G.Adj a d := e2.1.1
    have g3 : G.Adj b d := e3.1.1
    have c1 : c s(a, b) = n := e1.1.2
    have c2 : c s(a, d) = n := e2.1.2
    have c3 : c s(b, d) = n := e3.1.2
    have swapDA : s(d, a) = s(a, d) := Sym2.eq_swap
    have swapDB : s(d, b) = s(b, d) := Sym2.eq_swap
    have swapBA : s(b, a) = s(a, b) := Sym2.eq_swap
    have kmin_a : a ≤ b → a ≤ d → False := fun h1' h2' =>
      key a b d h1' h2' g1 g2 g3 (by rw [c1, c2])
    have kmin_b : b ≤ a → b ≤ d → False := fun h1' h2' =>
      key b a d h1' h2' g1.symm g3 g2 (by rw [swapBA, c1, c3])
    have kmin_d : d ≤ a → d ≤ b → False := fun h1' h2' =>
      key d a b h1' h2' g2.symm g3.symm g1 (by rw [swapDA, swapDB, c2, c3])
    rcases le_total a b with hab' | hab'
    · rcases le_total a d with had' | had'
      · exact kmin_a hab' had'
      · exact kmin_d had' (le_trans had' hab')
    · rcases le_total b d with hbd' | hbd'
      · exact kmin_b hab' hbd'
      · exact kmin_d (le_trans hbd' hab') hbd'
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem erdos595_countable_lower_neighbourhood {V : Type} [LinearOrder V] (G : SimpleGraph V) :
    (∀ u : V, Set.Countable {w : V | G.Adj u w ∧ w < u}) → IsCUTF G := by
  classical
  intro hcount
  have hcol : ∀ u : V, ∃ g : V → ℕ, ∀ a b : V, a < u → b < u → G.Adj u a → G.Adj u b →
      G.Adj a b → g a ≠ g b := by
    intro u
    haveI : Countable {w : V // G.Adj u w ∧ w < u} := (hcount u).to_subtype
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat {w : V // G.Adj u w ∧ w < u}
    refine ⟨fun x => if hx : G.Adj u x ∧ x < u then f ⟨x, hx⟩ else 0, ?_⟩
    intro a b hau hbu hua hub hab
    simp only [dif_pos (⟨hua, hau⟩ : G.Adj u a ∧ a < u),
      dif_pos (⟨hub, hbu⟩ : G.Adj u b ∧ b < u)]
    exact fun hc => G.ne_of_adj hab (congrArg Subtype.val (hf hc))
  choose g hg using hcol
  set F : V → V → ℕ := fun a b => if a ≤ b then g b a else g a b with hF
  have hsymm : ∀ a b : V, F a b = F b a := by
    intro a b
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · rcases le_total a b with h | h
      · have h2 : ¬ b ≤ a := fun hc => hne (le_antisymm h hc)
        simp [hF, h, h2]
      · have h2 : ¬ a ≤ b := fun hc => hne (le_antisymm hc h)
        simp [hF, h, h2]
  set c : Sym2 V → ℕ := Sym2.lift ⟨F, hsymm⟩ with hc
  have hcval : ∀ a b : V, c s(a, b) = F a b := by intro a b; rfl
  have key : ∀ u x y : V, x ≤ u → y ≤ u → G.Adj u x → G.Adj u y → G.Adj x y →
      c s(x, u) = c s(y, u) → False := by
    intro u x y hxu hyu h1 h2 h3 heq
    rw [hcval, hcval, hF] at heq
    simp only [if_pos hxu, if_pos hyu] at heq
    exact hg u x y (lt_of_le_of_ne hxu (G.ne_of_adj h1).symm)
      (lt_of_le_of_ne hyu (G.ne_of_adj h2).symm) h1 h2 h3 heq
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    have g1 : G.Adj a b := e1.1.1
    have g2 : G.Adj a d := e2.1.1
    have g3 : G.Adj b d := e3.1.1
    have c1 : c s(a, b) = n := e1.1.2
    have c2 : c s(a, d) = n := e2.1.2
    have c3 : c s(b, d) = n := e3.1.2
    have swapAB : s(a, b) = s(b, a) := Sym2.eq_swap
    have swapAD : s(a, d) = s(d, a) := Sym2.eq_swap
    have swapBD : s(b, d) = s(d, b) := Sym2.eq_swap
    have kmax_a : b ≤ a → d ≤ a → False := fun h1' h2' =>
      key a b d h1' h2' g1 g2 g3 (by rw [← swapAB, c1, ← swapAD, c2])
    have kmax_b : a ≤ b → d ≤ b → False := fun h1' h2' =>
      key b a d h1' h2' g1.symm g3 g2 (by rw [c1, ← swapBD, c3])
    have kmax_d : a ≤ d → b ≤ d → False := fun h1' h2' =>
      key d a b h1' h2' g2.symm g3.symm g1 (by rw [c2, c3])
    rcases le_total a b with hab' | hab'
    · rcases le_total b d with hbd' | hbd'
      · exact kmax_d (le_trans hab' hbd') hbd'
      · exact kmax_b hab' hbd'
    · rcases le_total a d with had' | had'
      · exact kmax_d had' (le_trans hab' had')
      · exact kmax_a hab' had'
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem erdos595_ordering_bound_general {V : Type} {I : Type} [LinearOrder V] (G : SimpleGraph V) :
    (∀ u : V, ∃ g : V → I, ∀ a b : V, u < a → u < b → G.Adj u a → G.Adj u b → G.Adj a b → g a ≠ g b) → IsUTF I G := by
  classical
  intro hnb
  choose g hg using hnb
  set F : V → V → I := fun a b => if a ≤ b then g a b else g b a with hF
  have hsymm : ∀ a b : V, F a b = F b a := by
    intro a b
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · rcases le_total a b with h | h
      · have h2 : ¬ b ≤ a := fun hc => hne (le_antisymm h hc)
        simp [hF, h, h2]
      · have h2 : ¬ a ≤ b := fun hc => hne (le_antisymm hc h)
        simp [hF, h, h2]
  set c : Sym2 V → I := Sym2.lift ⟨F, hsymm⟩ with hc
  have hcval : ∀ a b : V, c s(a, b) = F a b := by intro a b; rfl
  have key : ∀ u x y : V, u ≤ x → u ≤ y → G.Adj u x → G.Adj u y → G.Adj x y →
      c s(u, x) = c s(u, y) → False := by
    intro u x y hux huy h1 h2 h3 heq
    rw [hcval, hcval, hF] at heq
    simp only [if_pos hux, if_pos huy] at heq
    have hlx : u < x := lt_of_le_of_ne hux (G.ne_of_adj h1)
    have hly : u < y := lt_of_le_of_ne huy (G.ne_of_adj h2)
    exact hg u x y hlx hly h1 h2 h3 heq
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    have g1 : G.Adj a b := e1.1.1
    have g2 : G.Adj a d := e2.1.1
    have g3 : G.Adj b d := e3.1.1
    have c1 : c s(a, b) = n := e1.1.2
    have c2 : c s(a, d) = n := e2.1.2
    have c3 : c s(b, d) = n := e3.1.2
    have swapDA : s(d, a) = s(a, d) := Sym2.eq_swap
    have swapDB : s(d, b) = s(b, d) := Sym2.eq_swap
    have swapBA : s(b, a) = s(a, b) := Sym2.eq_swap
    have kmin_a : a ≤ b → a ≤ d → False := fun h1' h2' =>
      key a b d h1' h2' g1 g2 g3 (by rw [c1, c2])
    have kmin_b : b ≤ a → b ≤ d → False := fun h1' h2' =>
      key b a d h1' h2' g1.symm g3 g2 (by rw [swapBA, c1, c3])
    have kmin_d : d ≤ a → d ≤ b → False := fun h1' h2' =>
      key d a b h1' h2' g2.symm g3.symm g1 (by rw [swapDA, swapDB, c2, c3])
    rcases le_total a b with hab' | hab'
    · rcases le_total a d with had' | had'
      · exact kmin_a hab' had'
      · exact kmin_d had' (le_trans had' hab')
    · rcases le_total b d with hbd' | hbd'
      · exact kmin_b hab' hbd'
      · exact kmin_d (le_trans hbd' hab') hbd'
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem erdos595_successor_cardinal_bound {V : Type} {I : Type} [LinearOrder V] (G : SimpleGraph V) :
    (∀ u : V, ∃ f : V → I, ∀ a b : V, a < u → b < u → a ≠ b → f a ≠ f b) → IsUTF I G := by
  classical
  intro hinj
  have hcol : ∀ u : V, ∃ g : V → I, ∀ a b : V, a < u → b < u → G.Adj u a → G.Adj u b →
      G.Adj a b → g a ≠ g b := by
    intro u
    obtain ⟨f, hf⟩ := hinj u
    exact ⟨f, fun a b hau hbu _ _ hab => hf a b hau hbu (G.ne_of_adj hab)⟩
  choose g hg using hcol
  set F : V → V → I := fun a b => if a ≤ b then g b a else g a b with hF
  have hsymm : ∀ a b : V, F a b = F b a := by
    intro a b
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · rcases le_total a b with h | h
      · have h2 : ¬ b ≤ a := fun hc => hne (le_antisymm h hc)
        simp [hF, h, h2]
      · have h2 : ¬ a ≤ b := fun hc => hne (le_antisymm hc h)
        simp [hF, h, h2]
  set c : Sym2 V → I := Sym2.lift ⟨F, hsymm⟩ with hc
  have hcval : ∀ a b : V, c s(a, b) = F a b := by intro a b; rfl
  have key : ∀ u x y : V, x ≤ u → y ≤ u → G.Adj u x → G.Adj u y → G.Adj x y →
      c s(x, u) = c s(y, u) → False := by
    intro u x y hxu hyu h1 h2 h3 heq
    rw [hcval, hcval, hF] at heq
    simp only [if_pos hxu, if_pos hyu] at heq
    exact hg u x y (lt_of_le_of_ne hxu (G.ne_of_adj h1).symm)
      (lt_of_le_of_ne hyu (G.ne_of_adj h2).symm) h1 h2 h3 heq
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    have g1 : G.Adj a b := e1.1.1
    have g2 : G.Adj a d := e2.1.1
    have g3 : G.Adj b d := e3.1.1
    have c1 : c s(a, b) = n := e1.1.2
    have c2 : c s(a, d) = n := e2.1.2
    have c3 : c s(b, d) = n := e3.1.2
    have swapAB : s(a, b) = s(b, a) := Sym2.eq_swap
    have swapAD : s(a, d) = s(d, a) := Sym2.eq_swap
    have swapBD : s(b, d) = s(d, b) := Sym2.eq_swap
    have kmax_a : b ≤ a → d ≤ a → False := fun h1' h2' =>
      key a b d h1' h2' g1 g2 g3 (by rw [← swapAB, c1, ← swapAD, c2])
    have kmax_b : a ≤ b → d ≤ b → False := fun h1' h2' =>
      key b a d h1' h2' g1.symm g3 g2 (by rw [c1, ← swapBD, c3])
    have kmax_d : a ≤ d → b ≤ d → False := fun h1' h2' =>
      key d a b h1' h2' g2.symm g3.symm g1 (by rw [c2, c3])
    rcases le_total a b with hab' | hab'
    · rcases le_total b d with hbd' | hbd'
      · exact kmax_d (le_trans hab' hbd') hbd'
      · exact kmax_b hab' hbd'
    · rcases le_total a d with had' | had'
      · exact kmax_d had' (le_trans hab' had')
      · exact kmax_a hab' had'
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem erdos595_tc_le_tau_general {V I : Type} (G : SimpleGraph V) :
    G.CliqueFree 4 → (∀ H : SimpleGraph V, H ≤ G → H.CliqueFree 3 → ∃ f : V → I, IsProperI H f) → IsUTF I G := by
  classical
  intro hK4 htau
  letI : LinearOrder V := IsWellOrder.linearOrder (WellOrderingRel (α := V))
  refine erdos595_ordering_bound_general (I := I) G (fun u => ?_)
  set Hu : SimpleGraph V :=
    G ⊓ SimpleGraph.fromRel (fun a b => G.Adj u a ∧ G.Adj u b) with hHu
  have hle : Hu ≤ G := inf_le_left
  have hadj : ∀ a b : V, Hu.Adj a b → G.Adj a b ∧ G.Adj u a ∧ G.Adj u b := by
    intro a b h
    rw [hHu, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj] at h
    refine ⟨h.1, ?_⟩
    rcases h.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h1⟩
  have hmk : ∀ a b : V, G.Adj a b → G.Adj u a → G.Adj u b → Hu.Adj a b := by
    intro a b h1 h2 h3
    rw [hHu, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
    exact ⟨h1, G.ne_of_adj h1, Or.inl ⟨h2, h3⟩⟩
  have hfree : Hu.CliqueFree 3 := by
    intro t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    obtain ⟨g1, hua, hub⟩ := hadj a b (hcl ha hb hab)
    obtain ⟨g2, -, hud⟩ := hadj a d (hcl ha hd had)
    obtain ⟨g3, -, -⟩ := hadj b d (hcl hb hd hbd)
    have h3c : G.IsNClique 3 {a, b, d} :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨g1, g2, g3⟩
    refine hK4 (insert u {a, b, d}) (h3c.insert ?_)
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hua
    · exact hub
    · exact hud
  obtain ⟨f, hf⟩ := htau Hu hle hfree
  exact ⟨f, fun a b _ _ hua hub hab => hf a b (hmk a b hab hua hub)⟩

theorem erdos595_cone_two_layers {V : Type} (G : SimpleGraph V) (v : V) :
    (∀ a b c : V, a ≠ v → b ≠ v → c ≠ v → G.Adj a b → G.Adj a c → G.Adj b c → False) → G.CliqueFree 4 ∧ IsCUTF G := by
  classical
  intro hT
  constructor
  · intro t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hteq⟩ := Finset.card_eq_four.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hc : c ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    by_cases hav : a = v
    · subst hav
      exact hT b c d (fun h => hab h.symm) (fun h => hac h.symm) (fun h => had h.symm)
        (hcl hb hc hbc) (hcl hb hd hbd) (hcl hc hd hcd)
    · by_cases hbv : b = v
      · subst hbv
        exact hT a c d hav (fun h => hbc h.symm) (fun h => hbd h.symm)
          (hcl ha hc hac) (hcl ha hd had) (hcl hc hd hcd)
      · by_cases hcv : c = v
        · subst hcv
          exact hT a b d hav hbv (fun h => hcd h.symm)
            (hcl ha hb hab) (hcl ha hd had) (hcl hb hd hbd)
        · exact hT a b c hav hbv hcv (hcl ha hb hab) (hcl ha hc hac) (hcl hb hc hbc)
  · set L0 : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ v ∉ e} with hL0
    set L1 : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ v ∈ e} with hL1
    have h0free : L0.CliqueFree 3 := by
      intro t ht
      obtain ⟨hcl, hcard⟩ := ht
      obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ t := by rw [hteq]; simp
      have hb : b ∈ t := by rw [hteq]; simp
      have hc : c ∈ t := by rw [hteq]; simp
      have e1 := hcl ha hb hab
      have e2 := hcl ha hc hac
      have e3 := hcl hb hc hbc
      rw [hL0, SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
      have hav : a ≠ v := fun h => e1.1.2 (by rw [← h]; exact Sym2.mem_mk_left a b)
      have hbv : b ≠ v := fun h => e1.1.2 (by rw [← h]; exact Sym2.mem_mk_right a b)
      have hcv : c ≠ v := fun h => e2.1.2 (by rw [← h]; exact Sym2.mem_mk_right a c)
      exact hT a b c hav hbv hcv e1.1.1 e2.1.1 e3.1.1
    have h1free : L1.CliqueFree 3 := by
      intro t ht
      obtain ⟨hcl, hcard⟩ := ht
      obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ t := by rw [hteq]; simp
      have hb : b ∈ t := by rw [hteq]; simp
      have hc : c ∈ t := by rw [hteq]; simp
      have e1 := hcl ha hb hab
      have e2 := hcl ha hc hac
      have e3 := hcl hb hc hbc
      rw [hL1, SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
      have m1 : v = a ∨ v = b := by simpa [Sym2.mem_iff] using e1.1.2
      have m2 : v = a ∨ v = c := by simpa [Sym2.mem_iff] using e2.1.2
      have m3 : v = b ∨ v = c := by simpa [Sym2.mem_iff] using e3.1.2
      rcases m1 with rfl | rfl
      · rcases m3 with rfl | rfl
        · exact hab rfl
        · exact hac rfl
      · rcases m2 with rfl | rfl
        · exact hab rfl
        · exact hbc rfl
    refine ⟨fun n => Nat.casesOn n L0 (fun _ => L1), ?_, ?_⟩
    · rintro (_ | k)
      · exact h0free
      · exact h1free
    · ext a b
      rw [SimpleGraph.iSup_adj]
      constructor
      · intro hab
        by_cases hv : v ∈ s(a, b)
        · refine ⟨1, ?_⟩
          show L1.Adj a b
          rw [hL1, SimpleGraph.fromEdgeSet_adj]
          exact ⟨⟨hab, hv⟩, G.ne_of_adj hab⟩
        · refine ⟨0, ?_⟩
          show L0.Adj a b
          rw [hL0, SimpleGraph.fromEdgeSet_adj]
          exact ⟨⟨hab, hv⟩, G.ne_of_adj hab⟩
      · rintro ⟨n, hn⟩
        rcases n with _ | k
        · have : L0.Adj a b := hn
          rw [hL0, SimpleGraph.fromEdgeSet_adj] at this
          exact this.1.1
        · have : L1.Adj a b := hn
          rw [hL1, SimpleGraph.fromEdgeSet_adj] at this
          exact this.1.1

theorem erdos595_link_independence {V : Type} (G : SimpleGraph V) :
    G.CliqueFree 4 ↔ ∀ a b : V, G.Adj a b → ∀ x ∈ Link G a b, ∀ y ∈ Link G a b, x ≠ y → ¬ G.Adj x y := by
  classical
  constructor
  · intro hK4 a b hab x hx y hy hxy hxyadj
    obtain ⟨hax, hbx⟩ := hx
    obtain ⟨hay, hby⟩ := hy
    have h3 : G.IsNClique 3 {a, x, y} :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨hax, hay, hxyadj⟩
    refine hK4 (insert b {a, x, y}) (h3.insert ?_)
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hab.symm
    · exact hbx
    · exact hby
  · intro hlink t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, x, y, hab, hax, hay, hbx, hby, hxy, hteq⟩ := Finset.card_eq_four.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hx : x ∈ t := by rw [hteq]; simp
    have hy : y ∈ t := by rw [hteq]; simp
    exact hlink a b (hcl ha hb hab) x ⟨hcl ha hx hax, hcl hb hx hbx⟩
      y ⟨hcl ha hy hay, hcl hb hy hby⟩ hxy (hcl hx hy hxy)

theorem erdos595_subadditivity {V : Type} {I J : Type} (G : SimpleGraph V) (F : I → SimpleGraph V) (hG : G = ⨆ i, F i) :
    (∀ i, IsUTF J (F i)) → IsUTF (I × J) G := by
  classical
  intro hsub
  choose H hfree hEq using hsub
  refine ⟨fun p => H p.1 p.2, fun p => hfree p.1 p.2, ?_⟩
  ext a b
  rw [SimpleGraph.iSup_adj]
  constructor
  · intro hab
    rw [hG, SimpleGraph.iSup_adj] at hab
    obtain ⟨i, hi⟩ := hab
    rw [hEq i, SimpleGraph.iSup_adj] at hi
    obtain ⟨j, hj⟩ := hi
    exact ⟨(i, j), hj⟩
  · rintro ⟨p, hp⟩
    rw [hG, SimpleGraph.iSup_adj]
    refine ⟨p.1, ?_⟩
    rw [hEq p.1, SimpleGraph.iSup_adj]
    exact ⟨p.2, hp⟩

theorem erdos595_hereditary_dispersion {V C I : Type} (P : SimpleGraph V → Prop) (G : SimpleGraph V) :
    (∀ H₁ H₂ : SimpleGraph V, H₁ ≤ H₂ → P H₂ → P H₁) → (∀ H : SimpleGraph V, H ≤ G → P H → ∃ f : V → C, IsProperC H f) → (∀ f : V → (I → C), ¬ IsProperC G f) → ¬ ∃ H : I → SimpleGraph V, (∀ i, P (H i)) ∧ G = ⨆ i, H i := by
  classical
  intro hP htau hchi
  rintro ⟨H, hHP, hEq⟩
  have hle : ∀ i, H i ≤ G := by
    intro i
    rw [hEq]
    exact le_iSup H i
  choose f hf using fun i => htau (H i) (hle i) (hHP i)
  refine hchi (fun v => fun i => f i v) ?_
  intro a b hab hcon
  rw [hEq, SimpleGraph.iSup_adj] at hab
  obtain ⟨i, hi⟩ := hab
  exact hf i a b hi (congrFun hcon i)

theorem erdos595_triangle_adjacency {V : Type} (G : SimpleGraph V) :
    (∃ c : Sym2 V → ℕ, ∀ a b d : V, G.Adj a b → G.Adj a d → G.Adj b d → c s(a, b) ≠ c s(a, d)) → IsCUTF G := by
  classical
  rintro ⟨c, hc⟩
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    exact hc a b d e1.1.1 e2.1.1 e3.1.1 (by rw [e1.1.2, e2.1.2])
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem erdos595_triangle_adjacency_general {V : Type} {I : Type} (G : SimpleGraph V) :
    (∃ c : Sym2 V → I, ∀ a b d : V, G.Adj a b → G.Adj a d → G.Adj b d → c s(a, b) ≠ c s(a, d)) → IsUTF I G := by
  classical
  rintro ⟨c, hc⟩
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    exact hc a b d e1.1.1 e2.1.1 e3.1.1 (by rw [e1.1.2, e2.1.2])
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hn
      exact hn.1.1

theorem erdos595_transversal_ceiling {V C : Type} (G : SimpleGraph V) :
    (∀ D : Set (Sym2 V), IsTransversal G D → ∃ f : V → C, IsProperC (G.deleteEdges D) f) ↔ (∀ H : SimpleGraph V, H ≤ G → H.CliqueFree 3 → ∃ f : V → C, IsProperC H f) := by
  classical
  constructor
  · intro hD H hHle hHfree
    obtain ⟨f, hf⟩ := hD {e | e ∈ G.edgeSet ∧ e ∉ H.edgeSet} (by
      intro a b c hab hac hbc
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2, h3⟩ := hcon
      have m1 : H.Adj a b := by
        by_contra hx
        exact h1 ⟨hab, fun hy => hx hy⟩
      have m2 : H.Adj a c := by
        by_contra hx
        exact h2 ⟨hac, fun hy => hx hy⟩
      have m3 : H.Adj b c := by
        by_contra hx
        exact h3 ⟨hbc, fun hy => hx hy⟩
      exact hHfree {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨m1, m2, m3⟩))
    refine ⟨f, fun a b hab => hf a b ?_⟩
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hHle hab, fun hmem => hmem.2 hab⟩
  · intro hH D hDtr
    refine hH (G.deleteEdges D) (SimpleGraph.deleteEdges_le D) ?_
    intro t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, c, hab, hac, hbc, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hc : c ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hc hac
    have e3 := hcl hb hc hbc
    rw [SimpleGraph.deleteEdges_adj] at e1 e2 e3
    rcases hDtr a b c e1.1 e2.1 e3.1 with h | h | h
    · exact e1.2 h
    · exact e2.2 h
    · exact e3.2 h

theorem erdos595_locally_countable_component {W : Type} (T : SimpleGraph W) :
    (∀ v : W, (T.neighborSet v).Countable) → ∀ w : W, {x : W | T.Reachable w x}.Countable := by
  classical
  intro h w
  set B : ℕ → Set W := fun n => Nat.rec ({w} : Set W)
    (fun _ prev => prev ∪ ⋃ v ∈ prev, T.neighborSet v) n with hB
  have hBc : ∀ n, (B n).Countable := by
    intro n
    induction n with
    | zero => exact Set.countable_singleton w
    | succ k ih => exact ih.union (ih.biUnion (fun v _ => h v))
  have hstep : ∀ (c x : W), T.Adj c x → (∃ n, c ∈ B n) → ∃ n, x ∈ B n := by
    rintro c x hcx ⟨n, hn⟩
    exact ⟨n + 1, Or.inr (Set.mem_biUnion hn hcx)⟩
  have hrtg : ∀ x : W, Relation.ReflTransGen T.Adj w x → ∃ n, x ∈ B n := by
    intro x hx
    induction hx with
    | refl => exact ⟨0, rfl⟩
    | tail hprev hadj ih => exact hstep _ _ hadj ih
  refine Set.Countable.mono (fun x hx => ?_) (Set.countable_iUnion hBc)
  obtain ⟨n, hn⟩ := hrtg x ((SimpleGraph.reachable_iff_reflTransGen w x).mp hx)
  exact Set.mem_iUnion.2 ⟨n, hn⟩

theorem erdos595_countable_links {V : Type} (G : SimpleGraph V) (T : SimpleGraph (Sym2 V)) :
    (∀ a b d : V, G.Adj a b → G.Adj a d → G.Adj b d → s(a, b) ≠ s(a, d) → T.Adj s(a, b) s(a, d)) → (∀ e : Sym2 V, (T.neighborSet e).Countable) → IsCUTF G := by
  classical
  intro hT hloc
  have hcomp : ∀ q : T.ConnectedComponent,
      {x : Sym2 V | T.connectedComponentMk x = q}.Countable := by
    intro q
    obtain ⟨r, hr⟩ := Quot.exists_rep q
    have hset : {x : Sym2 V | T.connectedComponentMk x = q} = {x | T.Reachable r x} := by
      ext x
      constructor
      · intro hx
        have hxr : T.connectedComponentMk x = T.connectedComponentMk r := hx.trans hr.symm
        exact (SimpleGraph.ConnectedComponent.exact hxr).symm
      · intro hx
        have hxr : T.connectedComponentMk x = T.connectedComponentMk r :=
          SimpleGraph.ConnectedComponent.sound hx.symm
        exact hxr.trans hr
    rw [hset]
    exact erdos595_locally_countable_component T hloc r
  have hinj : ∀ q : T.ConnectedComponent,
      ∃ g : Sym2 V → ℕ, ∀ x y : Sym2 V, T.connectedComponentMk x = q →
        T.connectedComponentMk y = q → g x = g y → x = y := by
    intro q
    haveI : Countable {x : Sym2 V // T.connectedComponentMk x = q} := (hcomp q).to_subtype
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat {x : Sym2 V // T.connectedComponentMk x = q}
    refine ⟨fun x => if hx : T.connectedComponentMk x = q then f ⟨x, hx⟩ else 0, ?_⟩
    intro x y hx hy hxy
    simp only [dif_pos hx, dif_pos hy] at hxy
    exact congrArg Subtype.val (hf hxy)
  choose g hg using hinj
  refine erdos595_triangle_adjacency G ⟨fun e => g (T.connectedComponentMk e) e, ?_⟩
  intro a b d hab had hbd hcon
  have hne : s(a, b) ≠ s(a, d) := by
    intro hEq
    rw [Sym2.eq_iff] at hEq
    rcases hEq with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact (G.ne_of_adj hbd) h2
    · exact (G.ne_of_adj hab) h2.symm
  have hadj : T.Adj s(a, b) s(a, d) := hT a b d hab had hbd hne
  have hsame : T.connectedComponentMk s(a, b) = T.connectedComponentMk s(a, d) :=
    SimpleGraph.ConnectedComponent.sound hadj.reachable
  refine hne (hg (T.connectedComponentMk s(a, b)) s(a, b) s(a, d) rfl hsame.symm ?_)
  simpa [hsame] using hcon

theorem erdos595_dispersion_crosscheck {V : Type} {C : Type} (G : SimpleGraph V) (htau : ∀ H : SimpleGraph V, H ≤ G → H.CliqueFree 3 → ∃ f : V → C, IsProperC H f) (hchi : ∀ f : V → (ℕ → C), ¬ IsProperC G f) :
    ¬ IsCUTF G := by
  classical
  rintro ⟨H, hfree, hEq⟩
  have hle : ∀ i, H i ≤ G := by
    intro i; rw [hEq]; exact le_iSup H i
  choose f hf using fun i => htau (H i) (hle i) (hfree i)
  refine hchi (fun v => fun i => f i v) ?_
  rw [hEq]
  intro a b hab hcon
  rw [SimpleGraph.iSup_adj] at hab
  obtain ⟨i, hi⟩ := hab
  exact hf i a b hi (congrFun hcon i)

theorem erdos595_vertex_partition_bound {V I : Type} (G : SimpleGraph V) (rho : V → I) :
    (∀ a b d : V, rho a = rho b → rho b = rho d → G.Adj a b → G.Adj a d → G.Adj b d → False) → IsUTF (Sym2 I) G := by
  classical
  intro h
  have key : ∀ x y z : I, s(x, y) = s(x, z) → s(x, z) = s(y, z) → x = y ∧ y = z := by
    intro x y z h1 h2
    rcases Sym2.eq_iff.mp h1 with ⟨-, hyz⟩ | ⟨hxz, hyx⟩
    · rcases Sym2.eq_iff.mp h2 with ⟨hxy, -⟩ | ⟨hxz', hzy⟩
      · exact ⟨hxy, hyz⟩
      · exact ⟨hxz'.trans hzy, hyz⟩
    · exact ⟨hyx.symm, hyx.trans hxz⟩
  refine ⟨fun p => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ Sym2.map rho e = p}, ?_, ?_⟩
  · intro p t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    have q1 : s(rho a, rho b) = s(rho a, rho d) := by
      have t1 : Sym2.map rho s(a, b) = p := e1.1.2
      have t2 : Sym2.map rho s(a, d) = p := e2.1.2
      simpa [Sym2.map_pair_eq] using t1.trans t2.symm
    have q2 : s(rho a, rho d) = s(rho b, rho d) := by
      have t2 : Sym2.map rho s(a, d) = p := e2.1.2
      have t3 : Sym2.map rho s(b, d) = p := e3.1.2
      simpa [Sym2.map_pair_eq] using t2.trans t3.symm
    obtain ⟨hx, hy⟩ := key (rho a) (rho b) (rho d) q1 q2
    exact h a b d hx hy e1.1.1 e2.1.1 e3.1.1
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨Sym2.map rho s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨p, hp⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hp
      exact hp.1.1

theorem erdos595_countable_dominating {V : Type} (G : SimpleGraph V) (D : ℕ → V) :
    G.CliqueFree 4 → (∀ x : V, ∃ k : ℕ, x = D k ∨ G.Adj (D k) x) → IsUTF (Sym2 (ℕ × Bool)) G := by
  classical
  intro hK4 hdom
  set n : V → ℕ := fun x => Nat.find (hdom x) with hn
  have hspec : ∀ x : V, x = D (n x) ∨ G.Adj (D (n x)) x := fun x => Nat.find_spec (hdom x)
  set rho : V → ℕ × Bool := fun x => (n x, decide (x = D (n x))) with hrho
  have key : ∀ a b d : V, rho a = rho b → rho b = rho d →
      G.Adj a b → G.Adj a d → G.Adj b d → False := by
    intro a b d h1 h2 g1 g2 g3
    have hn1 : n a = n b := congrArg Prod.fst h1
    have hn2 : n b = n d := congrArg Prod.fst h2
    have hb1 : decide (a = D (n a)) = decide (b = D (n b)) := congrArg Prod.snd h1
    by_cases ha : a = D (n a)
    · have hb : b = D (n b) := by
        by_contra hbb
        rw [decide_eq_true ha, decide_eq_false hbb] at hb1
        exact Bool.noConfusion hb1
      exact (G.ne_of_adj g1) (ha.trans (by rw [hn1] ; exact hb.symm))
    · have hb : ¬ b = D (n b) := by
        intro hbb
        have hb2 : decide (b = D (n b)) = decide (a = D (n a)) := hb1.symm
        rw [decide_eq_true hbb, decide_eq_false ha] at hb2
        exact Bool.noConfusion hb2
      have hd : ¬ d = D (n d) := by
        intro hdd
        have hb3 : decide (b = D (n b)) = decide (d = D (n d)) := congrArg Prod.snd h2
        rw [decide_eq_true hdd, decide_eq_false hb] at hb3
        exact Bool.noConfusion hb3
      have ea : G.Adj (D (n a)) a := (hspec a).resolve_left ha
      have eb : G.Adj (D (n a)) b := by rw [hn1]; exact (hspec b).resolve_left hb
      have ed : G.Adj (D (n a)) d := by rw [hn1, hn2]; exact (hspec d).resolve_left hd
      have h3c : G.IsNClique 3 {a, b, d} :=
        SimpleGraph.is3Clique_triple_iff.mpr ⟨g1, g2, g3⟩
      refine hK4 (insert (D (n a)) {a, b, d}) (h3c.insert ?_)
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ea
      · exact eb
      · exact ed
  exact erdos595_vertex_partition_bound G rho key

theorem erdos595_dominating_general {V I : Type} (G : SimpleGraph V) (D : I → V) :
    G.CliqueFree 4 → (∀ x : V, ∃ i : I, x = D i ∨ G.Adj (D i) x) → IsUTF (Sym2 (I × Bool)) G := by
  classical
  intro hK4 hdom
  choose n hspec using hdom
  set rho : V → I × Bool := fun x => (n x, decide (x = D (n x))) with hrho
  have key : ∀ a b d : V, rho a = rho b → rho b = rho d →
      G.Adj a b → G.Adj a d → G.Adj b d → False := by
    intro a b d h1 h2 g1 g2 g3
    have hn1 : n a = n b := congrArg Prod.fst h1
    have hn2 : n b = n d := congrArg Prod.fst h2
    have hb1 : decide (a = D (n a)) = decide (b = D (n b)) := congrArg Prod.snd h1
    by_cases ha : a = D (n a)
    · have hb : b = D (n b) := by
        by_contra hbb
        rw [decide_eq_true ha, decide_eq_false hbb] at hb1
        exact Bool.noConfusion hb1
      exact (G.ne_of_adj g1) (ha.trans (by rw [hn1] ; exact hb.symm))
    · have hb : ¬ b = D (n b) := by
        intro hbb
        have hb2 : decide (b = D (n b)) = decide (a = D (n a)) := hb1.symm
        rw [decide_eq_true hbb, decide_eq_false ha] at hb2
        exact Bool.noConfusion hb2
      have hd : ¬ d = D (n d) := by
        intro hdd
        have hb3 : decide (b = D (n b)) = decide (d = D (n d)) := congrArg Prod.snd h2
        rw [decide_eq_true hdd, decide_eq_false hb] at hb3
        exact Bool.noConfusion hb3
      have ea : G.Adj (D (n a)) a := (hspec a).resolve_left ha
      have eb : G.Adj (D (n a)) b := by rw [hn1]; exact (hspec b).resolve_left hb
      have ed : G.Adj (D (n a)) d := by rw [hn1, hn2]; exact (hspec d).resolve_left hd
      have h3c : G.IsNClique 3 {a, b, d} :=
        SimpleGraph.is3Clique_triple_iff.mpr ⟨g1, g2, g3⟩
      refine hK4 (insert (D (n a)) {a, b, d}) (h3c.insert ?_)
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ea
      · exact eb
      · exact ed
  exact erdos595_vertex_partition_bound G rho key

theorem erdos595_interference_bound {V I J : Type} (G : SimpleGraph V) (D : I → V) (col : I → J) :
    G.CliqueFree 4 → (∀ x : V, ∃ i : I, x = D i ∨ G.Adj (D i) x) → (∀ i j : I, col i = col j → i ≠ j → ∀ x y : V, (x = D i ∨ G.Adj (D i) x) → (y = D j ∨ G.Adj (D j) y) → ¬ G.Adj x y) → IsUTF (Sym2 (J × Bool)) G := by
  classical
  intro hK4 hdom hsep
  choose n hspec using hdom
  refine erdos595_vertex_partition_bound G (fun x => (col (n x), decide (x = D (n x)))) ?_
  intro a b d h1 h2 g1 g2 g3
  have hc1 : col (n a) = col (n b) := congrArg Prod.fst h1
  have hc2 : col (n b) = col (n d) := congrArg Prod.fst h2
  have hnab : n a = n b := by
    by_contra hne
    exact hsep (n a) (n b) hc1 hne a b (hspec a) (hspec b) g1
  have hnbd : n b = n d := by
    by_contra hne
    exact hsep (n b) (n d) hc2 hne b d (hspec b) (hspec d) g3
  have hnad : n a = n d := hnab.trans hnbd
  have hb1 : decide (a = D (n a)) = decide (b = D (n b)) := congrArg Prod.snd h1
  have hb2 : decide (b = D (n b)) = decide (d = D (n d)) := congrArg Prod.snd h2
  by_cases ha : a = D (n a)
  · have hb : b = D (n b) := by
      by_contra hbb
      rw [decide_eq_true ha, decide_eq_false hbb] at hb1
      exact Bool.noConfusion hb1
    exact (G.ne_of_adj g1) (ha.trans (by rw [hnab]; exact hb.symm))
  · have hb : ¬ b = D (n b) := by
      intro hbb
      have := hb1.symm
      rw [decide_eq_true hbb, decide_eq_false ha] at this
      exact Bool.noConfusion this
    have hd : ¬ d = D (n d) := by
      intro hdd
      rw [decide_eq_true hdd, decide_eq_false hb] at hb2
      exact Bool.noConfusion hb2
    have ea : G.Adj (D (n a)) a := (hspec a).resolve_left ha
    have eb : G.Adj (D (n a)) b := by rw [hnab]; exact (hspec b).resolve_left hb
    have ed : G.Adj (D (n a)) d := by rw [hnad]; exact (hspec d).resolve_left hd
    refine hK4 (insert (D (n a)) {a, b, d})
      ((SimpleGraph.is3Clique_triple_iff.mpr ⟨g1, g2, g3⟩).insert ?_)
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ea
    · exact eb
    · exact ed

theorem erdos595_component_reduction {V I K : Type} (G : SimpleGraph V) (part : V → K) (H : K → I → SimpleGraph V) :
    (∀ a b : V, G.Adj a b → part a = part b) → (∀ k i, (H k i).CliqueFree 3) → (∀ k i a b, (H k i).Adj a b → part a = k) → (∀ a b : V, G.Adj a b → ∃ i, (H (part a) i).Adj a b) → (∀ k i, H k i ≤ G) → IsUTF I G := by
  classical
  intro hsep hfree hin hcov hle
  refine ⟨fun i => ⨆ k : K, H k i, ?_, ?_⟩
  · intro i t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    obtain ⟨k1, e1⟩ := SimpleGraph.iSup_adj.mp (hcl ha hb hab)
    obtain ⟨k2, e2⟩ := SimpleGraph.iSup_adj.mp (hcl ha hd had)
    obtain ⟨k3, e3⟩ := SimpleGraph.iSup_adj.mp (hcl hb hd hbd)
    have p1 : part a = k1 := hin k1 i a b e1
    have p2 : part a = k2 := hin k2 i a d e2
    have p3 : part b = k3 := hin k3 i b d e3
    have pb : part b = k1 := hin k1 i b a e1.symm
    have hk12 : k1 = k2 := p1.symm.trans p2
    have hk13 : k1 = k3 := pb.symm.trans p3
    subst hk12
    subst hk13
    exact hfree k1 i {a, b, d} (SimpleGraph.is3Clique_triple_iff.mpr ⟨e1, e2, e3⟩)
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      obtain ⟨i, hi⟩ := hcov a b hab
      exact ⟨i, SimpleGraph.iSup_adj.mpr ⟨part a, hi⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨k, hk⟩ := SimpleGraph.iSup_adj.mp hi
      exact hle k i hk

theorem erdos595_top_vertex_bound {V I : Type} [LinearOrder V] (G : SimpleGraph V) (f : V → I) :
    (∀ x y z : V, x < y → y < z → G.Adj x y → G.Adj x z → G.Adj y z → f y ≠ f z) → IsUTF I G := by
  classical
  intro htop
  set F : V → V → I := fun a b => if a ≤ b then f b else f a with hF
  have hsymm : ∀ a b : V, F a b = F b a := by
    intro a b
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · rcases le_total a b with h | h
      · have h2 : ¬ b ≤ a := fun hc => hne (le_antisymm h hc)
        simp [hF, h, h2]
      · have h2 : ¬ a ≤ b := fun hc => hne (le_antisymm hc h)
        simp [hF, h, h2]
  set c : Sym2 V → I := Sym2.lift ⟨F, hsymm⟩ with hc
  have hcval : ∀ a b : V, c s(a, b) = F a b := by intro a b; rfl
  refine ⟨fun p => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = p}, ?_, ?_⟩
  · intro p t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have e1 := hcl ha hb hab
    have e2 := hcl ha hd had
    have e3 := hcl hb hd hbd
    rw [SimpleGraph.fromEdgeSet_adj] at e1 e2 e3
    have g1 : G.Adj a b := e1.1.1
    have g2 : G.Adj a d := e2.1.1
    have g3 : G.Adj b d := e3.1.1
    have c1 : c s(a, b) = p := e1.1.2
    have c2 : c s(a, d) = p := e2.1.2
    have c3 : c s(b, d) = p := e3.1.2
    have key : ∀ x y z : V, x ≤ y → y ≤ z → G.Adj x y → G.Adj x z → G.Adj y z →
        c s(x, z) = c s(y, z) → c s(x, y) = c s(x, z) → False := by
      intro x y z hxy hyz gxy gxz gyz h1 h2
      have hxz : x ≤ z := le_trans hxy hyz
      have v1 : c s(x, y) = f y := by rw [hcval, hF]; simp [hxy]
      have v2 : c s(x, z) = f z := by rw [hcval, hF]; simp [hxz]
      have hne : y ≠ z := G.ne_of_adj gyz
      have hlt : y < z := lt_of_le_of_ne hyz hne
      have hltx : x < y := lt_of_le_of_ne hxy (G.ne_of_adj gxy)
      exact htop x y z hltx hlt gxy gxz gyz (by rw [← v1, ← v2, h2])
    rcases le_total a b with hab' | hab'
    · rcases le_total b d with hbd' | hbd'
      · exact key a b d hab' hbd' g1 g2 g3 (by rw [c2, c3]) (by rw [c1, c2])
      · rcases le_total a d with had' | had'
        · exact key a d b had' hbd' g2 g1 g3.symm (by rw [c1, Sym2.eq_swap (a := d), c3]) (by rw [c2, c1])
        · exact key d a b had' hab' g2.symm g3.symm g1
            (by rw [Sym2.eq_swap (a := d), c3, c1]) (by rw [Sym2.eq_swap (a := d), c2, Sym2.eq_swap (a := d), c3])
    · rcases le_total a d with had' | had'
      · exact key b a d hab' had' g1.symm g3 g2 (by rw [c3, c2]) (by rw [Sym2.eq_swap (a := b), c1, c3])
      · rcases le_total b d with hbd' | hbd'
        · exact key b d a hbd' had' g3 g1.symm g2.symm
            (by rw [Sym2.eq_swap (a := b), c1, Sym2.eq_swap (a := d), c2]) (by rw [c3, Sym2.eq_swap (a := b), c1])
        · exact key d b a hbd' hab' g3.symm g2.symm g1.symm
            (by rw [Sym2.eq_swap (a := d), c2, Sym2.eq_swap (a := b), c1]) (by rw [Sym2.eq_swap (a := d), c3, Sym2.eq_swap (a := d), c2])
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      exact ⟨c s(a, b), by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨hab, rfl⟩, G.ne_of_adj hab⟩⟩
    · rintro ⟨p, hp⟩
      rw [SimpleGraph.fromEdgeSet_adj] at hp
      exact hp.1.1

theorem erdos595_monotone_general {V I : Type} (G H : SimpleGraph V) :
    H ≤ G → IsUTF I G → IsUTF I H := by
  classical
  rintro hle ⟨L, hfree, hEq⟩
  refine ⟨fun i => H ⊓ L i, fun i => (hfree i).anti inf_le_right, ?_⟩
  ext a b
  rw [SimpleGraph.iSup_adj]
  constructor
  · intro hab
    have hG : G.Adj a b := hle hab
    rw [hEq, SimpleGraph.iSup_adj] at hG
    obtain ⟨i, hi⟩ := hG
    exact ⟨i, ⟨hab, hi⟩⟩
  · rintro ⟨i, hi⟩
    exact hi.1

theorem erdos595_continuum_blindness {V : Type} (G : SimpleGraph V) (e : V → (ℕ → Bool)) :
    Function.Injective e → IsCUTF G := by
  classical
  intro he
  have hdiff : ∀ a b : V, G.Adj a b → ∃ n : ℕ, e a n ≠ e b n := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    exact (G.ne_of_adj hab) (he (funext hcon))
  refine ⟨fun n => SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, Nat.find (hdiff a b h) = n), ?_, ?_⟩
  · intro n t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have get : ∀ x y : V, (SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, Nat.find (hdiff a b h) = n)).Adj x y →
        e x n ≠ e y n := by
      intro x y hxy
      rw [SimpleGraph.fromRel_adj] at hxy
      rcases hxy.2 with ⟨h, hn⟩ | ⟨h, hn⟩
      · have := Nat.find_spec (hdiff x y h)
        rw [hn] at this; exact this
      · have := Nat.find_spec (hdiff y x h)
        rw [hn] at this; exact fun hc => this hc.symm
    have d1 := get a b (hcl ha hb hab)
    have d2 := get a d (hcl ha hd had)
    have d3 := get b d (hcl hb hd hbd)
    rcases Bool.eq_false_or_eq_true (e a n) with h | h <;>
      rcases Bool.eq_false_or_eq_true (e b n) with h' | h' <;>
      rcases Bool.eq_false_or_eq_true (e d n) with h'' | h'' <;>
      simp_all
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      refine ⟨Nat.find (hdiff a b hab), ?_⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨G.ne_of_adj hab, Or.inl ⟨hab, rfl⟩⟩
    · rintro ⟨n, hn⟩
      rw [SimpleGraph.fromRel_adj] at hn
      rcases hn.2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact h.symm

theorem erdos595_power_blindness_general {V I : Type} (G : SimpleGraph V) (e : V → (I → Bool)) :
    Function.Injective e → IsUTF I G := by
  classical
  intro he
  have hdiff : ∀ a b : V, G.Adj a b → ∃ i : I, e a i ≠ e b i := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    exact (G.ne_of_adj hab) (he (funext hcon))
  choose ch hch using hdiff
  refine ⟨fun i => SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, ch a b h = i), ?_, ?_⟩
  · intro i t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have get : ∀ x y : V,
        (SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, ch a b h = i)).Adj x y →
        e x i ≠ e y i := by
      intro x y hxy
      rw [SimpleGraph.fromRel_adj] at hxy
      rcases hxy.2 with ⟨h, hn⟩ | ⟨h, hn⟩
      · have hs := hch x y h
        rw [hn] at hs
        exact hs
      · have hs := hch y x h
        rw [hn] at hs
        exact fun hc => hs hc.symm
    have d1 := get a b (hcl ha hb hab)
    have d2 := get a d (hcl ha hd had)
    have d3 := get b d (hcl hb hd hbd)
    rcases Bool.eq_false_or_eq_true (e a i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (e b i) with h' | h' <;>
      rcases Bool.eq_false_or_eq_true (e d i) with h'' | h'' <;>
      simp_all
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      refine ⟨ch a b hab, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨G.ne_of_adj hab, Or.inl ⟨hab, rfl⟩⟩
    · rintro ⟨i, hi⟩
      rw [SimpleGraph.fromRel_adj] at hi
      rcases hi.2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact h.symm

theorem erdos595_partition_lower_bound {V I : Type} (G : SimpleGraph V) :
    ¬ IsUTF (Sym2 I) G → ¬ ∃ rho : V → I, ∀ a b d : V, rho a = rho b → rho b = rho d → G.Adj a b → G.Adj a d → G.Adj b d → False := by
  intro hnot hex
  obtain ⟨rho, hrho⟩ := hex
  exact hnot (erdos595_vertex_partition_bound G rho hrho)

theorem erdos595_reindex {V I J : Type} (G : SimpleGraph V) (s : J → I) :
    Function.Surjective s → IsUTF I G → IsUTF J G := by
  rintro hs ⟨L, hfree, hEq⟩
  refine ⟨fun j => L (s j), fun j => hfree _, ?_⟩
  ext a b
  rw [hEq, SimpleGraph.iSup_adj, SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := hs i
    exact ⟨j, hi⟩
  · rintro ⟨j, hj⟩
    exact ⟨s j, hj⟩

theorem erdos595_proper_binary_cover {V I : Type} (G : SimpleGraph V) (e : V → (I → Bool)) :
    (∀ a b : V, G.Adj a b → e a ≠ e b) → IsUTF I G := by
  classical
  intro he
  have hdiff : ∀ a b : V, G.Adj a b → ∃ i : I, e a i ≠ e b i := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    exact he a b hab (funext hcon)
  choose ch hch using hdiff
  refine ⟨fun i => SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, ch a b h = i), ?_, ?_⟩
  · intro i t ht
    obtain ⟨hcl, hcard⟩ := ht
    obtain ⟨a, b, d, hab, had, hbd, hteq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ t := by rw [hteq]; simp
    have hb : b ∈ t := by rw [hteq]; simp
    have hd : d ∈ t := by rw [hteq]; simp
    have get : ∀ x y : V,
        (SimpleGraph.fromRel (fun a b => ∃ h : G.Adj a b, ch a b h = i)).Adj x y →
        e x i ≠ e y i := by
      intro x y hxy
      rw [SimpleGraph.fromRel_adj] at hxy
      rcases hxy.2 with ⟨h, hn⟩ | ⟨h, hn⟩
      · have hs := hch x y h
        rw [hn] at hs
        exact hs
      · have hs := hch y x h
        rw [hn] at hs
        exact fun hc => hs hc.symm
    have d1 := get a b (hcl ha hb hab)
    have d2 := get a d (hcl ha hd had)
    have d3 := get b d (hcl hb hd hbd)
    rcases Bool.eq_false_or_eq_true (e a i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (e b i) with h' | h' <;>
      rcases Bool.eq_false_or_eq_true (e d i) with h'' | h'' <;>
      simp_all
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      refine ⟨ch a b hab, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨G.ne_of_adj hab, Or.inl ⟨hab, rfl⟩⟩
    · rintro ⟨i, hi⟩
      rw [SimpleGraph.fromRel_adj] at hi
      rcases hi.2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact h.symm

theorem erdos595_colour_interface {V I C : Type} (G : SimpleGraph V) (f : V → C) (g : C → (I → Bool)) :
    (∀ a b : V, G.Adj a b → f a ≠ f b) → Function.Injective g → IsUTF I G := by
  intro hf hg
  refine erdos595_proper_binary_cover G (fun v => g (f v)) ?_
  intro a b hab hcon
  exact hf a b hab (hg hcon)

theorem erdos595_pair_colouring_criterion {V I : Type} (G : SimpleGraph V) (c : V → V → I) :
    (∀ a b : V, c a b = c b a) → (∀ a b d : V, G.Adj a b → G.Adj a d → G.Adj b d → c a b ≠ c a d) → IsUTF I G := by
  intro hsymm h
  refine erdos595_triangle_adjacency_general G ⟨Sym2.lift ⟨c, hsymm⟩, ?_⟩
  intro a b d h1 h2 h3
  exact h a b d h1 h2 h3

def cosetColour : Fin 16 → Fin 3 :=
  ![0, 0, 1, 1, 2, 2, 2, 1, 0, 2, 0, 1, 0, 1, 2, 0]

/-- Colour the pair {a,b} of vertices of the complete graph on sixteen vertices by the
coset of their difference in the field of order sixteen, where the difference is the
bitwise exclusive or. -/

def k16Colour (a b : Fin 16) : Fin 3 :=
  cosetColour ⟨Nat.xor a.val b.val % 16, Nat.mod_lt _ (by norm_num)⟩

theorem erdos595_k16_three_cover :
    ∀ a b c : Fin 16, a ≠ b → a ≠ c → b ≠ c → ¬ (k16Colour a b = k16Colour a c ∧ k16Colour a c = k16Colour b c) := by decide

def adjC (a b : Fin 17) : Bool :=
  (a - b = 1) || (a - b = 2) || (a - b = 4) || (a - b = 8) ||
  (a - b = 9) || (a - b = 13) || (a - b = 15) || (a - b = 16)

def colC (a b : Fin 17) : Bool :=
  (a - b = 1) || (a - b = 4) || (a - b = 13) || (a - b = 16)

theorem erdos595_c17_two_cover :
    ∀ a b c : Fin 17, (adjC a b && adjC a c && adjC b c && (colC a b == colC a c) && (colC a c == colC b c)) = false := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 400000 in
theorem erdos595_c17_k4free :
    ∀ a b c d : Fin 17, (adjC a b && adjC a c && adjC a d && adjC b c && adjC b d && adjC c d) = false := by decide

/-- K5 is the union of two triangle-free subgraphs: the two 5-cycles given by the
difference classes {1,4} and {2,3}. Anchors the cover-number scale from below and is
consistent with R(3,3)=6. -/
def colK5 (a b : Fin 5) : Bool := (a - b = 1) || (a - b = 4)

theorem erdos595_k5_two_cover :
    ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      ((colK5 a b == colK5 a c) && (colK5 a c == colK5 b c)) = false := by
  decide


/-- LINK-CHROMATIC BOUND. The ceiling bound needs only the chromatic numbers of the LINK
subgraphs (each vertex's neighbourhood), not of every triangle-free subgraph. For a K4-free
graph every link is triangle-free, so this is at most tau, and it can be strictly smaller:
on the Paley graph of order 17 every link is 2-chromatic while tau is at least 4. This is
the exact reason the tau bound was measured loose. -/
theorem erdos595_link_chromatic_bound {V I : Type} [LinearOrder V] (G : SimpleGraph V) :
    (∀ u : V, ∃ g : V → I, ∀ a b : V, G.Adj u a → G.Adj u b → G.Adj a b → g a ≠ g b) →
    IsUTF I G := by
  intro h
  refine erdos595_ordering_bound_general (I := I) G (fun u => ?_)
  obtain ⟨g, hg⟩ := h u
  exact ⟨g, fun a b _ _ h1 h2 h3 => hg a b h1 h2 h3⟩

/-- Every link of a K4-free graph is triangle-free, so the link-chromatic bound subsumes
the ceiling bound. -/
theorem erdos595_link_triangle_free {V : Type} (G : SimpleGraph V) (hK4 : G.CliqueFree 4)
    (u : V) : ∀ a b c : V, G.Adj u a → G.Adj u b → G.Adj u c →
      G.Adj a b → G.Adj a c → G.Adj b c → False := by
  classical
  intro a b c hua hub huc hab hac hbc
  have h3c : G.IsNClique 3 {a, b, c} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩
  refine hK4 (insert u {a, b, c}) (h3c.insert ?_)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hua
  · exact hub
  · exact huc


/-- L595-03. ROOTED EDGELESS AMALGAMATION PRESERVES K4-FREENESS.
If every edge of G lies inside the P-side or inside the Q-side (so the only vertices
through which the two sides communicate are those satisfying both, the declared root),
and neither side contains a four-element clique of G, then G contains none either.
This is the invariant that protects the forbidden clique across a closure stage. -/
theorem erdos595_rooted_amalgam {V : Type} (G : SimpleGraph V) (P Q : V → Prop)
    (hcov : ∀ a b : V, G.Adj a b → (P a ∧ P b) ∨ (Q a ∧ Q b))
    (h1 : ∀ t : Finset V, (∀ x ∈ t, P x) → ¬ G.IsNClique 4 t)
    (h2 : ∀ t : Finset V, (∀ x ∈ t, Q x) → ¬ G.IsNClique 4 t) :
    G.CliqueFree 4 := by
  classical
  intro t ht
  obtain ⟨hcl, hcard⟩ := ht
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hteq⟩ := Finset.card_eq_four.mp hcard
  have ha : a ∈ t := by rw [hteq]; simp
  have hb : b ∈ t := by rw [hteq]; simp
  by_cases hall : ∀ x ∈ t, P x
  · exact h1 t hall ⟨hcl, hcard⟩
  · push_neg at hall
    obtain ⟨x, hx, hnx⟩ := hall
    have hQx : Q x := by
      by_cases hxa : x = a
      · have hxb : x ≠ b := by rw [hxa]; exact hab
        rcases hcov x b (hcl hx hb hxb) with ⟨hp, -⟩ | ⟨hq, -⟩
        · exact absurd hp hnx
        · exact hq
      · rcases hcov x a (hcl hx ha hxa) with ⟨hp, -⟩ | ⟨hq, -⟩
        · exact absurd hp hnx
        · exact hq
    refine h2 t (fun y hy => ?_) ⟨hcl, hcard⟩
    by_cases hyx : y = x
    · exact hyx ▸ hQx
    · rcases hcov x y (hcl hx hy (Ne.symm hyx)) with ⟨hp, -⟩ | ⟨-, hq⟩
      · exact absurd hp hnx
      · exact hq

/-- L595-04. TRANSFINITE UNION SAFETY. A directed union of K4-free graphs is K4-free,
because a four-element clique is a finite object and already appears at one stage. -/
theorem erdos595_directed_union_safe {V J : Type} (F : J → SimpleGraph V)
    (hdir : ∀ i j : J, ∃ k : J, F i ≤ F k ∧ F j ≤ F k)
    (hne : Nonempty J) (hfree : ∀ i, (F i).CliqueFree 4) :
    (⨆ i, F i).CliqueFree 4 := by
  classical
  intro t ht
  obtain ⟨hcl, hcard⟩ := ht
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hteq⟩ := Finset.card_eq_four.mp hcard
  have ha : a ∈ t := by rw [hteq]; simp
  have hb : b ∈ t := by rw [hteq]; simp
  have hc : c ∈ t := by rw [hteq]; simp
  have hd : d ∈ t := by rw [hteq]; simp
  have pick : ∀ u v : V, (⨆ i, F i).Adj u v → ∃ i, (F i).Adj u v := by
    intro u v huv
    rw [SimpleGraph.iSup_adj] at huv
    exact huv
  obtain ⟨i1, e1⟩ := pick a b (hcl ha hb hab)
  obtain ⟨i2, e2⟩ := pick a c (hcl ha hc hac)
  obtain ⟨i3, e3⟩ := pick a d (hcl ha hd had)
  obtain ⟨i4, e4⟩ := pick b c (hcl hb hc hbc)
  obtain ⟨i5, e5⟩ := pick b d (hcl hb hd hbd)
  obtain ⟨i6, e6⟩ := pick c d (hcl hc hd hcd)
  obtain ⟨j1, hj1a, hj1b⟩ := hdir i1 i2
  obtain ⟨j2, hj2a, hj2b⟩ := hdir i3 i4
  obtain ⟨j3, hj3a, hj3b⟩ := hdir i5 i6
  obtain ⟨k1, hk1a, hk1b⟩ := hdir j1 j2
  obtain ⟨k, hka, hkb⟩ := hdir k1 j3
  have f1 : (F k).Adj a b := hka (hk1a (hj1a e1))
  have f2 : (F k).Adj a c := hka (hk1a (hj1b e2))
  have f3 : (F k).Adj a d := hka (hk1b (hj2a e3))
  have f4 : (F k).Adj b c := hka (hk1b (hj2b e4))
  have f5 : (F k).Adj b d := hkb (hj3a e5)
  have f6 : (F k).Adj c d := hkb (hj3b e6)
  refine hfree k {a, b, c, d} ⟨?_, by rw [← hteq]; exact hcard⟩
  intro u hu v hv huv
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl huv
      | exact f1 | exact f2 | exact f3 | exact f4 | exact f5 | exact f6
      | exact f1.symm | exact f2.symm | exact f3.symm | exact f4.symm | exact f5.symm | exact f6.symm


/-- THE SIMULTANEITY OBSTRUCTION, exact form. In the Shelah assembly the monochromatic
triangle sits on designated vertices. If a single designated vertex were attached to each
INDEX and every two indices carried their cross edge, then any four indices would complete
a four-element clique. Hence the designated vertices must depend on the whole triple, and
distinct configurations must be kept vertex-disjoint outside their declared roots. This is
the precise reason the construction cannot be built by naive indexing. -/
theorem erdos595_designated_per_index_fails {V I : Type} (G : SimpleGraph V) (w : I → V)
    (hinj : Function.Injective w) (a b c d : I)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hadj : ∀ i j : I, i ≠ j → G.Adj (w i) (w j)) :
    ¬ G.CliqueFree 4 := by
  classical
  have H : ∀ i j : I, w i ≠ w j → G.Adj (w i) (w j) := by
    intro i j h
    exact hadj i j (fun e => h (by rw [e]))
  intro hfree
  refine hfree {w a, w b, w c, w d} ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      exact H _ _ hxy
  · refine Finset.card_eq_four.mpr ⟨w a, w b, w c, w d, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · exact fun h => hab (hinj h)
    · exact fun h => hac (hinj h)
    · exact fun h => had (hinj h)
    · exact fun h => hbc (hinj h)
    · exact fun h => hbd (hinj h)
    · exact fun h => hcd (hinj h)

end Erdos595Lib

#print axioms Erdos595Lib.erdos595_compactness_T26
#print axioms Erdos595Lib.erdos595_finite_obstruction_T27
#print axioms Erdos595Lib.erdos595_countable_core_T28
#print axioms Erdos595Lib.erdos595_countable_blindness
#print axioms Erdos595Lib.erdos595_bipartite_level_down
#print axioms Erdos595Lib.erdos595_arrow_form
#print axioms Erdos595Lib.erdos595_proper_edge_colouring
#print axioms Erdos595Lib.erdos595_neighbourhood_bound
#print axioms Erdos595Lib.erdos595_tc_le_tau
#print axioms Erdos595Lib.erdos595_chi_le_two_pow_tau
#print axioms Erdos595Lib.erdos595_upper_neighbourhood_bound
#print axioms Erdos595Lib.erdos595_countable_lower_neighbourhood
#print axioms Erdos595Lib.erdos595_ordering_bound_general
#print axioms Erdos595Lib.erdos595_successor_cardinal_bound
#print axioms Erdos595Lib.erdos595_tc_le_tau_general
#print axioms Erdos595Lib.erdos595_cone_two_layers
#print axioms Erdos595Lib.erdos595_link_independence
#print axioms Erdos595Lib.erdos595_subadditivity
#print axioms Erdos595Lib.erdos595_hereditary_dispersion
#print axioms Erdos595Lib.erdos595_triangle_adjacency
#print axioms Erdos595Lib.erdos595_triangle_adjacency_general
#print axioms Erdos595Lib.erdos595_transversal_ceiling
#print axioms Erdos595Lib.erdos595_locally_countable_component
#print axioms Erdos595Lib.erdos595_countable_links
#print axioms Erdos595Lib.erdos595_dispersion_crosscheck
#print axioms Erdos595Lib.erdos595_vertex_partition_bound
#print axioms Erdos595Lib.erdos595_countable_dominating
#print axioms Erdos595Lib.erdos595_dominating_general
#print axioms Erdos595Lib.erdos595_interference_bound
#print axioms Erdos595Lib.erdos595_component_reduction
#print axioms Erdos595Lib.erdos595_top_vertex_bound
#print axioms Erdos595Lib.erdos595_monotone_general
#print axioms Erdos595Lib.erdos595_continuum_blindness
#print axioms Erdos595Lib.erdos595_power_blindness_general
#print axioms Erdos595Lib.erdos595_partition_lower_bound
#print axioms Erdos595Lib.erdos595_reindex
#print axioms Erdos595Lib.erdos595_proper_binary_cover
#print axioms Erdos595Lib.erdos595_colour_interface
#print axioms Erdos595Lib.erdos595_pair_colouring_criterion
#print axioms Erdos595Lib.erdos595_k16_three_cover
#print axioms Erdos595Lib.erdos595_c17_two_cover
#print axioms Erdos595Lib.erdos595_c17_k4free
#print axioms Erdos595Lib.erdos595_k5_two_cover
#print axioms Erdos595Lib.erdos595_link_chromatic_bound
#print axioms Erdos595Lib.erdos595_link_triangle_free
#print axioms Erdos595Lib.erdos595_rooted_amalgam
#print axioms Erdos595Lib.erdos595_directed_union_safe
#print axioms Erdos595Lib.erdos595_designated_per_index_fails

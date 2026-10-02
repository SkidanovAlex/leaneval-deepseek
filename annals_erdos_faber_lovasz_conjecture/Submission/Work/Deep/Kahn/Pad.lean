import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The `C`-uniform padding of a linear hypergraph

Given a linear hypergraph `𝓗` on `Fin n` whose edges have size at most `C`, attach
`C - edgeSize e` fresh vertices to each edge `e` to obtain a `C`-uniform linear
hypergraph `padHyp C 𝓗` on the disjoint-union vertex type `(Fin n) ⊕ (𝓗 × Fin C)`.
This is the first step of the embedding (`prop:embedding`) of the Kahn
subproject: after padding the "image" of every edge has exactly `C` vertices.
-/

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture
open scoped BigOperators

noncomputable section

variable {n : ℕ}

abbrev PV (n C : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) : Type :=
  (Fin n) ⊕ (𝓗 × Fin C)

abbrev inlP (n C : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) :
    Fin n → PV n C 𝓗 := Sum.inl

abbrev inrP (n C : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) :
    (𝓗 × Fin C) → PV n C 𝓗 := Sum.inr

def padSlots (C : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (e : 𝓗) :
    Set (PV n C 𝓗) :=
  Set.image (inrP n C 𝓗) {p : 𝓗 × Fin C | p.1 = e ∧ p.2.val < C - edgeSize (e : Set (Fin n))}

def padEdge (C : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (e : 𝓗) :
    Set (PV n C 𝓗) :=
  Set.image (inlP n C 𝓗) (e : Set (Fin n)) ∪ padSlots C 𝓗 e

def padHyp (C : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) :
    ErdosFaberLovaszConjecture.Hypergraph (PV n C 𝓗) :=
  Set.range (padEdge C 𝓗)

theorem mem_padSlots {C : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {e : 𝓗} {v : PV n C 𝓗} :
    v ∈ padSlots C 𝓗 e ↔ ∃ p : 𝓗 × Fin C,
      p.1 = e ∧ p.2.val < C - edgeSize (e : Set (Fin n)) ∧ inrP n C 𝓗 p = v := by
  rw [padSlots]
  constructor
  · rintro ⟨p, hp, hpv⟩
    exact ⟨p, hp.1, hp.2, hpv⟩
  · rintro ⟨p, h1, h2, hpv⟩
    exact ⟨p, ⟨h1, h2⟩, hpv⟩

theorem padSlots_ncard (C : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (e : 𝓗) : (padSlots C 𝓗 e).ncard = C - edgeSize (e : Set (Fin n)) := by
  classical
  have himg : (padSlots C 𝓗 e).ncard =
      ({p : 𝓗 × Fin C | p.1 = e ∧ p.2.val < C - edgeSize (e : Set (Fin n))} : Set (𝓗 × Fin C)).ncard :=
    Set.ncard_image_of_injective _ (Sum.inr_injective (α := Fin n) (β := 𝓗 × Fin C))
  rw [himg]
  have hbij : ({p : 𝓗 × Fin C | p.1 = e ∧ p.2.val < C - edgeSize (e : Set (Fin n))} : Set (𝓗 × Fin C))
      = Set.image (fun i : Fin (C - edgeSize (e : Set (Fin n))) =>
          ((e, ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le C _)⟩) : 𝓗 × Fin C)) Set.univ := by
    ext p
    constructor
    · rintro ⟨rfl, hp⟩
      exact ⟨⟨p.2.val, hp⟩, Set.mem_univ _, by simp⟩
    · rintro ⟨i, -, hi⟩
      rw [← hi]
      exact ⟨rfl, i.isLt⟩
  rw [hbij, Set.ncard_image_of_injective _ ?_, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  intro i j h
  exact Fin.ext (congrArg (fun x : 𝓗 × Fin C => x.2.val) h)

theorem padEdge_ncard {C : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (hC : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C) (e : 𝓗) :
    (padEdge C 𝓗 e).ncard = C := by
  classical
  have hdisj : Disjoint (Set.image (inlP n C 𝓗) (e : Set (Fin n))) (padSlots C 𝓗 e) := by
    rw [Set.disjoint_left]
    rintro v ⟨x, -, rfl⟩ ⟨p, -, h⟩
    exact absurd h (by simp)
  have h1 : (Set.image (inlP n C 𝓗) (e : Set (Fin n))).ncard = edgeSize (e : Set (Fin n)) := by
    rw [Set.ncard_image_of_injective _ (Sum.inl_injective (α := Fin n) (β := 𝓗 × Fin C)),
      edgeSize_eq_ncard]
  rw [padEdge, Set.ncard_union_eq hdisj, h1, padSlots_ncard]
  have := hC e
  omega

theorem padEdge_injective {C : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (hC : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C) :
    Function.Injective (padEdge C 𝓗) := by
  classical
  have key : ∀ e f : 𝓗, padEdge C 𝓗 e = padEdge C 𝓗 f →
      (e : Set (Fin n)) ⊆ (f : Set (Fin n)) := by
    intro e f h x hx
    have hmem : (inlP n C 𝓗 x) ∈ padEdge C 𝓗 f := by
      rw [← h]
      exact Set.mem_union_left _ ⟨x, hx, rfl⟩
    rcases (Set.mem_union _ _ _).mp hmem with h' | h'
    · obtain ⟨y, hy, hyx⟩ := h'
      exact Sum.inl_injective hyx ▸ hy
    · obtain ⟨p, -, hpv⟩ := mem_padSlots.mp h'
      exact absurd hpv (by simp)
  intro e f h
  exact Subtype.ext (Set.Subset.antisymm (key e f h) (key f e h.symm))

theorem padHyp_linear {C : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) : (padHyp C 𝓗).Pairwise fun a b => (a ∩ b).Subsingleton := by
  rintro _ ⟨e, rfl⟩ _ ⟨f, rfl⟩ hef
  have hsub : padEdge C 𝓗 e ∩ padEdge C 𝓗 f ⊆
      Set.image (inlP n C 𝓗) ((e : Set (Fin n)) ∩ (f : Set (Fin n))) := by
    rintro v ⟨hv1, hv2⟩
    rcases (Set.mem_union _ _ _).mp hv1 with h1 | h1
    · obtain ⟨x, hx, rfl⟩ := h1
      rcases (Set.mem_union _ _ _).mp hv2 with h2 | h2
      · obtain ⟨y, hy, hyx⟩ := h2
        exact ⟨x, ⟨hx, Sum.inl_injective hyx ▸ hy⟩, rfl⟩
      · obtain ⟨q, hq1, hq2, hqv⟩ := mem_padSlots.mp h2
        exact absurd hqv Sum.inr_ne_inl
    · obtain ⟨p, hp1, hp2, hpv⟩ := mem_padSlots.mp h1
      rcases (Set.mem_union _ _ _).mp hv2 with h2 | h2
      · obtain ⟨y, hy1, hyv⟩ := h2
        exact absurd (hpv.trans hyv.symm) Sum.inr_ne_inl
      · obtain ⟨q, hq1, hq2, hqv⟩ := mem_padSlots.mp h2
        have hpq : p = q := Sum.inr_injective (hpv.trans hqv.symm)
        exact absurd (congrArg (padEdge C 𝓗) (hp1.symm.trans ((congrArg Prod.fst hpq).trans hq1))) hef
  intro v hv w hw
  obtain ⟨x, hx, rfl⟩ := hsub hv
  obtain ⟨y, hy, hy'⟩ := hsub hw
  have hne : (e : Set (Fin n)) ≠ (f : Set (Fin n)) :=
    fun h => hef (congrArg (padEdge C 𝓗) (Subtype.ext h))
  have : x = y := hlin e.2 f.2 hne hx hy
  rw [this, hy']

end
end Work.Deep.Kahn

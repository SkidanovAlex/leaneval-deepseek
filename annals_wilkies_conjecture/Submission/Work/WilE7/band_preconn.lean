import Mathlib

set_option autoImplicit false

namespace Work.WilE7

/-- The open vertical band `{p : X × ℝ | a p.1 < p.2 < b p.1}` (over the whole space `X`). -/
def bandSet {X : Type*} (a b : X → EReal) : Set (X × ℝ) :=
  {p | a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1}

/-- The vertical slice of the band over the point `x`. -/
def bandSlice {X : Type*} (x : X) (a b : X → EReal) : Set (X × ℝ) :=
  {p | p.1 = x ∧ a x < (p.2 : EReal) ∧ (p.2 : EReal) < b x}

/-- The set of base points `x` for which the slice of the band at `x` meets the open
set `u ⊆ X × ℝ`. -/
def bandBetweenMem {X : Type*} (a b : X → EReal) (u : Set (X × ℝ)) : Set X :=
  {x | ∃ y : ℝ, a x < (y : EReal) ∧ (y : EReal) < b x ∧ (x, y) ∈ u}

variable {X : Type*} [TopologicalSpace X]

lemma bandSlice_eq_prod (a b : X → EReal) (x : X) :
    bandSlice x a b = ({x} : Set X) ×ˢ {y : ℝ | a x < (y : EReal) ∧ (y : EReal) < b x} := by
  ext p
  simp only [bandSlice, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff, and_assoc]

lemma bandSlice_subset (a b : X → EReal) (x : X) : bandSlice x a b ⊆ bandSet a b := by
  intro p hp
  simp only [bandSlice, Set.mem_ofPred_eq] at hp
  simp only [bandSet, Set.mem_ofPred_eq]
  rw [hp.1]
  exact ⟨hp.2.1, hp.2.2⟩

/-- Every slice of the band is preconnected (it is an interval in the vertical direction). -/
lemma isPreconnected_bandSlice (a b : X → EReal) (x : X) :
    IsPreconnected (bandSlice x a b) := by
  rw [bandSlice_eq_prod]
  refine IsPreconnected.prod isPreconnected_singleton ?_
  rw [isPreconnected_iff_ordConnected, Set.ordConnected_iff]
  intro y₁ hy₁ y₂ hy₂ _ z hz
  simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hy₁ hy₂ hz ⊢
  exact ⟨hy₁.1.trans_le (EReal.coe_le_coe hz.1), (EReal.coe_le_coe hz.2).trans_lt hy₂.2⟩

/-- The set of base points whose slice meets an open set is open (when `a` and `b` are
continuous). -/
lemma isOpen_bandBetweenMem {a b : X → EReal} (ha : Continuous a) (hb : Continuous b)
    {u : Set (X × ℝ)} (hu : IsOpen u) : IsOpen (bandBetweenMem a b u) := by
  have heq : bandBetweenMem a b u
      = ⋃ y : ℝ, (a ⁻¹' Set.Iio (y : EReal)) ∩ (b ⁻¹' Set.Ioi (y : EReal)) ∩
          ((fun x : X => (x, y)) ⁻¹' u) := by
    ext x
    simp only [bandBetweenMem, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage]
    exact ⟨fun ⟨y, h1, h2, h3⟩ => ⟨y, ⟨⟨h1, h2⟩, h3⟩⟩,
      fun ⟨y, ⟨⟨h1, h2⟩, h3⟩⟩ => ⟨y, h1, h2, h3⟩⟩
  rw [heq]
  refine isOpen_iUnion fun y => ?_
  exact ((ha.isOpen_preimage _ (isOpen_Iio' _)).inter
    (hb.isOpen_preimage _ (isOpen_Ioi' _))).inter
    ((continuous_id.prodMk continuous_const).isOpen_preimage _ hu)

/-- The band over a preconnected space is preconnected. -/
theorem isPreconnected_bandSet [PreconnectedSpace X] {a b : X → EReal} (ha : Continuous a)
    (hb : Continuous b) (hab : ∀ x, a x < b x) : IsPreconnected (bandSet a b) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hdisj
  -- Each slice is contained in `u` or in `v`.
  have hdich : ∀ x : X, bandSlice x a b ⊆ u ∨ bandSlice x a b ⊆ v := by
    intro x
    refine isPreconnected_iff_subset_of_disjoint.mp (isPreconnected_bandSlice a b x) u v hu hv
      ((bandSlice_subset a b x).trans hsub) ?_
    rw [← Set.disjoint_iff_inter_eq_empty]
    exact (Set.disjoint_iff_inter_eq_empty.mpr hdisj).mono_left (bandSlice_subset a b x)
  -- The base points whose slice meets `u` (resp. `v`).
  have hP : IsOpen (bandBetweenMem a b u) := isOpen_bandBetweenMem ha hb hu
  have hQ : IsOpen (bandBetweenMem a b v) := isOpen_bandBetweenMem ha hb hv
  have hcover : (Set.univ : Set X) ⊆ bandBetweenMem a b u ∪ bandBetweenMem a b v := by
    intro x _
    obtain ⟨y, h1, h2⟩ := EReal.exists_between_coe_real (hab x)
    rcases hsub (show (x, y) ∈ bandSet a b from ⟨h1, h2⟩) with h | h
    · exact Or.inl ⟨y, h1, h2, h⟩
    · exact Or.inr ⟨y, h1, h2, h⟩
  have hdisjPQ : (Set.univ : Set X) ∩ (bandBetweenMem a b u ∩ bandBetweenMem a b v) = ∅ := by
    rw [Set.univ_inter, ← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, hxP, hxQ⟩
    simp only [bandBetweenMem, Set.mem_ofPred_eq] at hxP hxQ
    obtain ⟨y₁, ha₁, hb₁, hu₁⟩ := hxP
    obtain ⟨y₂, ha₂, hb₂, hv₂⟩ := hxQ
    rcases hdich x with h | h
    · have hmem : (x, y₂) ∈ bandSet a b ∩ (u ∩ v) :=
        ⟨⟨ha₂, hb₂⟩, h ⟨rfl, ha₂, hb₂⟩, hv₂⟩
      rw [hdisj] at hmem
      exact hmem
    · have hmem : (x, y₁) ∈ bandSet a b ∩ (u ∩ v) :=
        ⟨⟨ha₁, hb₁⟩, hu₁, h ⟨rfl, ha₁, hb₁⟩⟩
      rw [hdisj] at hmem
      exact hmem
  rcases isPreconnected_iff_subset_of_disjoint.mp
      (isPreconnected_univ : IsPreconnected (Set.univ : Set X))
      (bandBetweenMem a b u) (bandBetweenMem a b v) hP hQ hcover hdisjPQ with hUP | hUQ
  · left
    intro p hp
    simp only [bandSet, Set.mem_ofPred_eq] at hp
    have hxP : p.1 ∈ bandBetweenMem a b u := hUP (Set.mem_univ p.1)
    simp only [bandBetweenMem, Set.mem_ofPred_eq] at hxP
    obtain ⟨y, hay, hyb, hxy⟩ := hxP
    rcases hdich p.1 with hh | hh
    · exact hh ⟨rfl, hp.1, hp.2⟩
    · exfalso
      have hmem : (p.1, y) ∈ bandSet a b ∩ (u ∩ v) :=
        ⟨⟨hay, hyb⟩, hxy, hh ⟨rfl, hay, hyb⟩⟩
      rw [hdisj] at hmem
      exact hmem
  · right
    intro p hp
    simp only [bandSet, Set.mem_ofPred_eq] at hp
    have hxQ : p.1 ∈ bandBetweenMem a b v := hUQ (Set.mem_univ p.1)
    simp only [bandBetweenMem, Set.mem_ofPred_eq] at hxQ
    obtain ⟨y, hay, hyb, hxy⟩ := hxQ
    rcases hdich p.1 with hh | hh
    · exfalso
      have hmem : (p.1, y) ∈ bandSet a b ∩ (u ∩ v) :=
        ⟨⟨hay, hyb⟩, hh ⟨rfl, hay, hyb⟩, hxy⟩
      rw [hdisj] at hmem
      exact hmem
    · exact hh ⟨rfl, hp.1, hp.2⟩

theorem band_preconn {α : Type*} [TopologicalSpace α] {C : Set α} (hC : IsPreconnected C)
    {a b : α → EReal} (ha : ContinuousOn a C) (hb : ContinuousOn b C)
    (hab : ∀ x ∈ C, a x < b x) :
    IsPreconnected {p : α × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} := by
  haveI : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  have ha' : Continuous (fun x : C => a x.1) :=
    ha.comp_continuous continuous_subtype_val (fun x => x.2)
  have hb' : Continuous (fun x : C => b x.1) :=
    hb.comp_continuous continuous_subtype_val (fun x => x.2)
  have hcore : IsPreconnected (bandSet (fun x : C => a x.1) (fun x : C => b x.1)) :=
    isPreconnected_bandSet ha' hb' (fun x => hab x.1 x.2)
  have hcont : ContinuousOn (fun p : C × ℝ => (p.1.1, p.2))
      (bandSet (fun x : C => a x.1) (fun x : C => b x.1)) :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  have himg := hcore.image (fun p : C × ℝ => (p.1.1, p.2)) hcont
  have heq : (fun p : C × ℝ => (p.1.1, p.2)) ''
        bandSet (fun x : C => a x.1) (fun x : C => b x.1)
      = {p : α × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [bandSet, Set.mem_ofPred_eq] at hq
      exact ⟨q.1.2, hq.1, hq.2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(⟨p.1, h1⟩, p.2), by
        simp only [bandSet, Set.mem_ofPred_eq]
        exact ⟨h2, h3⟩, rfl⟩
  rw [heq] at himg
  exact himg

end Work.WilE7

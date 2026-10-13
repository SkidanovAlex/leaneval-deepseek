import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-! ## Preconnectedness of cylindrical cells and of the cube

The frozen cell decomposition `WilkiesDesign.IsCell` is built from three constructors:
the base cell `univ ⊆ ℝ⁰`, graphs of functions continuous on the base cell, and
"bands" between two continuous (extended-real valued) boundary functions.

Each of the three is preconnected: `univ ⊆ ℝ⁰` is a subsingleton; the graph of a
function over the base `C` is the image of `C` under the continuous map
`x ↦ Fin.snoc x (f x)`; and a band is the image of the region between the two
continuous functions, which is handled by the auxiliary lemma
`Work.WilE7.isPreconnected_band`.
-/

/-- The closed cube `[-1,1]^n` is preconnected: it is a product of intervals. -/
theorem isPreconnected_cubeC (n : ℕ) : IsPreconnected (cubeC n) := by
  have h : Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1) = cubeC n := by
    ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, Set.mem_ofPred_eq, cubeC,
      abs_le]
  rw [← h]
  exact isPreconnected_univ_pi fun _ => isPreconnected_Icc

/-- The base cell `ℝ⁰` is a subsingleton, hence preconnected. -/
theorem isPreconnected_cell_zero : IsPreconnected (Set.univ : Set (Fin 0 → ℝ)) :=
  Set.Subsingleton.isPreconnected Set.subsingleton_univ

/-- The region between two continuous extended-real valued functions `a < b` over a
preconnected base `C` is preconnected.

Over each point `x` of the base the region is the interval `(a x, b x)` in the vertical
direction, hence preconnected; and these intervals vary continuously with `x` (this is
where `hab` is used: it makes every fibre nonempty, so the base points whose fibre meets
one of two open sets covering the region do cover `C`). A separation of the region would
therefore separate the preconnected base `C`. -/
theorem isPreconnected_band {α : Type*} [TopologicalSpace α] {C : Set α} (hC : IsPreconnected C)
    {a b : α → EReal} (ha : ContinuousOn a C) (hb : ContinuousOn b C)
    (hab : ∀ x ∈ C, a x < b x) :
    IsPreconnected {p : α × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} := by
  haveI hpre : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  have ha' : Continuous fun x : C => a x.1 :=
    ha.comp_continuous continuous_subtype_val fun x => x.2
  have hb' : Continuous fun x : C => b x.1 :=
    hb.comp_continuous continuous_subtype_val fun x => x.2
  -- the vertical slice over a point `x` of the base is preconnected
  have hfib : ∀ x : C, IsPreconnected
      {q : C × ℝ | q.1 = x ∧ a x.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b x.1} := by
    intro x
    have hset : {q : C × ℝ | q.1 = x ∧ a x.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b x.1}
        = ({x} : Set C) ×ˢ {y : ℝ | a x.1 < (y : EReal) ∧ (y : EReal) < b x.1} := by
      ext q
      exact ⟨fun hq => ⟨hq.1, hq.2.1, hq.2.2⟩, fun hq => ⟨hq.1, hq.2.1, hq.2.2⟩⟩
    rw [hset]
    refine IsPreconnected.prod isPreconnected_singleton ?_
    refine Set.OrdConnected.isPreconnected ?_
    rw [Set.ordConnected_iff]
    intro y₁ hy₁ y₂ hy₂ _ z hz
    exact ⟨hy₁.1.trans_le (EReal.coe_le_coe_iff.mpr hz.1),
      (EReal.coe_le_coe_iff.mpr hz.2).trans_lt hy₂.2⟩
  -- the base points whose slice meets a given open set form an open set
  have hopen : ∀ u' : Set (C × ℝ), IsOpen u' → IsOpen
      {x : C | ∃ y : ℝ, a x.1 < (y : EReal) ∧ (y : EReal) < b x.1 ∧ (x, y) ∈ u'} := by
    intro u' hu'
    have heq : {x : C | ∃ y : ℝ, a x.1 < (y : EReal) ∧ (y : EReal) < b x.1 ∧ (x, y) ∈ u'}
        = ⋃ y : ℝ, ((fun x : C => a x.1) ⁻¹' Set.Iio (y : EReal)) ∩
            ((fun x : C => b x.1) ⁻¹' Set.Ioi (y : EReal)) ∩
            ((fun x : C => (x, y)) ⁻¹' u') := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_Iio, Set.mem_Ioi, and_assoc]
    rw [heq]
    refine isOpen_iUnion fun y => ?_
    exact ((ha'.isOpen_preimage _ (isOpen_Iio' _)).inter
      (hb'.isOpen_preimage _ (isOpen_Ioi' _))).inter
      ((continuous_id.prodMk continuous_const).isOpen_preimage _ hu')
  -- the region inside `C × ℝ`
  have hcore : IsPreconnected {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1} := by
    rw [isPreconnected_iff_subset_of_disjoint]
    intro u v hu hv hTuv hdisj
    let A : Set C := {x | ∃ y : ℝ, a x.1 < (y : EReal) ∧ (y : EReal) < b x.1 ∧ (x, y) ∈ u}
    let B : Set C := {x | ∃ y : ℝ, a x.1 < (y : EReal) ∧ (y : EReal) < b x.1 ∧ (x, y) ∈ v}
    have hAop : IsOpen A := hopen u hu
    have hBop : IsOpen B := hopen v hv
    have hcover : (Set.univ : Set C) ⊆ A ∪ B := by
      intro x _
      obtain ⟨y, h1, h2⟩ := EReal.exists_between_coe_real (hab x.1 x.2)
      rcases hTuv (show (x, y) ∈
          {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1} from ⟨h1, h2⟩) with h | h
      · exact Or.inl (show x ∈ A from ⟨y, h1, h2, h⟩)
      · exact Or.inr (show x ∈ B from ⟨y, h1, h2, h⟩)
    have hdisjAB : A ∩ B = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      rw [Set.mem_inter_iff] at hx
      obtain ⟨hxA, hxB⟩ := hx
      have hy₁ : ∃ y : ℝ, a x.1 < (y : EReal) ∧ (y : EReal) < b x.1 ∧ (x, y) ∈ u := hxA
      have hy₂ : ∃ y : ℝ, a x.1 < (y : EReal) ∧ (y : EReal) < b x.1 ∧ (x, y) ∈ v := hxB
      obtain ⟨y₁, h1, h2, h3⟩ := hy₁
      obtain ⟨y₂, h1', h2', h3'⟩ := hy₂
      have hGsub : {q : C × ℝ | q.1 = x ∧ a x.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b x.1} ⊆ u ∪ v := by
        rintro q ⟨hq1, hq2, hq3⟩
        refine hTuv ?_
        show a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1
        rw [hq1]
        exact ⟨hq2, hq3⟩
      have hGdisj : {q : C × ℝ | q.1 = x ∧ a x.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b x.1} ∩
          (u ∩ v) = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨q, hq⟩
        rw [Set.mem_inter_iff, Set.mem_inter_iff] at hq
        obtain ⟨hqS, hqu, hqv⟩ := hq
        obtain ⟨hq1, hq2, hq3⟩ := hqS
        have hT : q ∈ {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1} := by
          show a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1
          rw [hq1]
          exact ⟨hq2, hq3⟩
        have hmem : q ∈ {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1} ∩
            (u ∩ v) := ⟨hT, hqu, hqv⟩
        rw [hdisj] at hmem
        exact hmem
      rcases isPreconnected_iff_subset_of_disjoint.mp (hfib x) u v hu hv hGsub hGdisj with h | h
      · have hm : (x, y₂) ∈
            {q : C × ℝ | q.1 = x ∧ a x.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b x.1} ∩ (u ∩ v) :=
          ⟨⟨rfl, h1', h2'⟩, h ⟨rfl, h1', h2'⟩, h3'⟩
        rw [hGdisj] at hm
        exact hm
      · have hm : (x, y₁) ∈
            {q : C × ℝ | q.1 = x ∧ a x.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b x.1} ∩ (u ∩ v) :=
          ⟨⟨rfl, h1, h2⟩, h3, h ⟨rfl, h1, h2⟩⟩
        rw [hGdisj] at hm
        exact hm
    rcases isPreconnected_iff_subset_of_disjoint.mp
        (isPreconnected_univ : IsPreconnected (Set.univ : Set C)) A B hAop hBop hcover
        (by rw [Set.univ_inter]; exact hdisjAB) with hAall | hBall
    · left
      intro q hq
      have hy : ∃ y : ℝ, a q.1.1 < (y : EReal) ∧ (y : EReal) < b q.1.1 ∧ (q.1, y) ∈ u :=
        hAall (Set.mem_univ q.1)
      obtain ⟨y, h1, h2, h3⟩ := hy
      have hGsub : {q' : C × ℝ | q'.1 = q.1 ∧ a q.1.1 < (q'.2 : EReal) ∧
          (q'.2 : EReal) < b q.1.1} ⊆ u ∪ v := by
        rintro q' ⟨hq1, hq2, hq3⟩
        refine hTuv ?_
        show a q'.1.1 < (q'.2 : EReal) ∧ (q'.2 : EReal) < b q'.1.1
        rw [hq1]
        exact ⟨hq2, hq3⟩
      have hGdisj : {q' : C × ℝ | q'.1 = q.1 ∧ a q.1.1 < (q'.2 : EReal) ∧
          (q'.2 : EReal) < b q.1.1} ∩ (u ∩ v) = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨q', hq'⟩
        rw [Set.mem_inter_iff, Set.mem_inter_iff] at hq'
        obtain ⟨hq'S, hqu, hqv⟩ := hq'
        obtain ⟨hq1, hq2, hq3⟩ := hq'S
        have hT : q' ∈ {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1} := by
          show a q'.1.1 < (q'.2 : EReal) ∧ (q'.2 : EReal) < b q'.1.1
          rw [hq1]
          exact ⟨hq2, hq3⟩
        have hmem : q' ∈ {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1} ∩
            (u ∩ v) := ⟨hT, hqu, hqv⟩
        rw [hdisj] at hmem
        exact hmem
      rcases isPreconnected_iff_subset_of_disjoint.mp (hfib q.1) u v hu hv hGsub hGdisj with h | h
      · exact h ⟨rfl, hq.1, hq.2⟩
      · exfalso
        have hm : (q.1, y) ∈
            {q' : C × ℝ | q'.1 = q.1 ∧ a q.1.1 < (q'.2 : EReal) ∧ (q'.2 : EReal) < b q.1.1} ∩
            (u ∩ v) := ⟨⟨rfl, h1, h2⟩, h3, h ⟨rfl, h1, h2⟩⟩
        rw [hGdisj] at hm
        exact hm
    · right
      intro q hq
      have hy : ∃ y : ℝ, a q.1.1 < (y : EReal) ∧ (y : EReal) < b q.1.1 ∧ (q.1, y) ∈ v :=
        hBall (Set.mem_univ q.1)
      obtain ⟨y, h1, h2, h3⟩ := hy
      have hGsub : {q' : C × ℝ | q'.1 = q.1 ∧ a q.1.1 < (q'.2 : EReal) ∧
          (q'.2 : EReal) < b q.1.1} ⊆ u ∪ v := by
        rintro q' ⟨hq1, hq2, hq3⟩
        refine hTuv ?_
        show a q'.1.1 < (q'.2 : EReal) ∧ (q'.2 : EReal) < b q'.1.1
        rw [hq1]
        exact ⟨hq2, hq3⟩
      have hGdisj : {q' : C × ℝ | q'.1 = q.1 ∧ a q.1.1 < (q'.2 : EReal) ∧
          (q'.2 : EReal) < b q.1.1} ∩ (u ∩ v) = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨q', hq'⟩
        rw [Set.mem_inter_iff, Set.mem_inter_iff] at hq'
        obtain ⟨hq'S, hqu, hqv⟩ := hq'
        obtain ⟨hq1, hq2, hq3⟩ := hq'S
        have hT : q' ∈ {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1} := by
          show a q'.1.1 < (q'.2 : EReal) ∧ (q'.2 : EReal) < b q'.1.1
          rw [hq1]
          exact ⟨hq2, hq3⟩
        have hmem : q' ∈ {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1} ∩
            (u ∩ v) := ⟨hT, hqu, hqv⟩
        rw [hdisj] at hmem
        exact hmem
      rcases isPreconnected_iff_subset_of_disjoint.mp (hfib q.1) u v hu hv hGsub hGdisj with h | h
      · exfalso
        have hm : (q.1, y) ∈
            {q' : C × ℝ | q'.1 = q.1 ∧ a q.1.1 < (q'.2 : EReal) ∧ (q'.2 : EReal) < b q.1.1} ∩
            (u ∩ v) := ⟨⟨rfl, h1, h2⟩, h ⟨rfl, h1, h2⟩, h3⟩
        rw [hGdisj] at hm
        exact hm
      · exact h ⟨rfl, hq.1, hq.2⟩
  -- transport along `C × ℝ → α × ℝ`
  have hcont : ContinuousOn (fun q : C × ℝ => (q.1.1, q.2))
      {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1} :=
    (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd).continuousOn
  have heq : (fun q : C × ℝ => (q.1.1, q.2)) ''
        {q : C × ℝ | a q.1.1 < (q.2 : EReal) ∧ (q.2 : EReal) < b q.1.1}
      = {p : α × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1.2, hq.1, hq.2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(⟨p.1, h1⟩, p.2), ⟨h2, h3⟩, rfl⟩
  rw [← heq]
  exact hcore.image _ hcont

/-- A graph cell over a preconnected base is preconnected. -/
theorem isPreconnected_graph {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsPreconnected C)
    (f : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f C) :
    IsPreconnected {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} := by
  have hcont : ContinuousOn (fun x : Fin n → ℝ => (Fin.snoc x (f x) : Fin (n + 1) → ℝ)) C := by
    intro x hx
    exact (continuous_id.continuousWithinAt).finSnoc (hf x hx)
  have hset : {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}
      = (fun x : Fin n → ℝ => (Fin.snoc x (f x) : Fin (n + 1) → ℝ)) '' C := by
    ext z
    constructor
    · intro hz
      refine ⟨Fin.init z, hz.1, ?_⟩
      show Fin.snoc (Fin.init z) (f (Fin.init z)) = z
      rw [← hz.2]
      exact Fin.snoc_init_self z
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simpa using hx, by simp⟩
  rw [hset]
  exact hC.image _ hcont

/-- A band cell over a preconnected base is preconnected. -/
theorem isPreconnected_band_fin {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsPreconnected C)
    (a b : (Fin n → ℝ) → EReal) (ha : ContinuousOn a C) (hb : ContinuousOn b C)
    (hab : ∀ x ∈ C, a x < b x) :
    IsPreconnected {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
  have hband : IsPreconnected
      {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} :=
    isPreconnected_band hC ha hb hab
  have hcont : ContinuousOn
      (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ))
      {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} :=
    ((Continuous.finSnoc (A := fun _ : Fin (n + 1) => ℝ) continuous_fst
      continuous_snd)).continuousOn
  have hset : {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)}
      = (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) ''
          {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} := by
    ext z
    constructor
    · intro hz
      refine ⟨(Fin.init z, z (Fin.last n)), hz, ?_⟩
      exact Fin.snoc_init_self z
    · rintro ⟨p, hp, rfl⟩
      simpa [Fin.init_snoc, Fin.snoc_last] using hp
  rw [hset]
  exact hband.image _ hcont

/-- Every cylindrical cell is preconnected. -/
theorem isPreconnected_of_isCell : ∀ {n : ℕ} {c : Set (Fin n → ℝ)}, IsCell n c → IsPreconnected c := by
  intro n c h
  induction h with
  | zero => exact isPreconnected_cell_zero
  | graph hC f hf ih => exact isPreconnected_graph ih f hf
  | band hC a b ha hb hab ih => exact isPreconnected_band_fin ih a b ha hb hab

/-! ## Elementary properties of a cylindrical decomposition on a set -/

/-- Every cell of a cylindrical decomposition of `A` is contained in `A`. -/
theorem isCylDecompOn_subset : ∀ {n : ℕ} {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
    IsCylDecompOn n A C → ∀ κ ∈ C, κ ⊆ A := by
  intro n
  induction n with
  | zero =>
      intro A C h κ hκ
      rcases h with ⟨hA, hC⟩ | ⟨hA, hC⟩
      · subst hA; subst hC
        rw [Finset.mem_singleton] at hκ
        subst hκ
        exact Set.subset_univ _
      · subst hC
        exact absurd hκ (Finset.notMem_empty κ)
  | succ n _ =>
      intro A C h κ hκ
      obtain ⟨-, -, hU, -⟩ := h
      rw [← hU]
      exact Set.subset_sUnion_of_mem hκ

/-- A cylindrical decomposition of `A` covers `A`. -/
theorem isCylDecompOn_sUnion : ∀ {n : ℕ} {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
    IsCylDecompOn n A C → ⋃₀ (C : Set (Set (Fin n → ℝ))) = A := by
  intro n
  induction n with
  | zero =>
      intro A C h
      rcases h with ⟨hA, hC⟩ | ⟨hA, hC⟩ <;> (subst hA; subst hC; simp)
  | succ n _ =>
      intro A C h
      exact h.2.2.1

/-- The cells of a cylindrical decomposition of `A` are nonempty. -/
theorem isCylDecompOn_nonempty : ∀ {n : ℕ} {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
    IsCylDecompOn n A C → ∀ κ ∈ C, κ.Nonempty := by
  intro n
  induction n with
  | zero =>
      intro A C h κ hκ
      rcases h with ⟨hA, hC⟩ | ⟨hA, hC⟩
      · subst hC
        rw [Finset.mem_singleton] at hκ
        subst hκ
        exact ⟨fun i => i.elim0, trivial⟩
      · subst hC
        exact absurd hκ (Finset.notMem_empty κ)
  | succ n _ =>
      intro A C h κ hκ
      exact (h.1 κ hκ).2

theorem cells :
    (∀ {n : ℕ} {c : Set (Fin n → ℝ)}, WilkiesDesign.IsCell n c → IsPreconnected c) ∧
    (∀ n : ℕ, IsPreconnected (WilkiesDesign.E.cubeC n)) ∧
    (∀ {n : ℕ} {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
        WilkiesDesign.E.IsCylDecompOn n A C → ∀ κ ∈ C, κ ⊆ A) ∧
    (∀ {n : ℕ} {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
        WilkiesDesign.E.IsCylDecompOn n A C → ⋃₀ (C : Set (Set (Fin n → ℝ))) = A) ∧
    (∀ {n : ℕ} {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))},
        WilkiesDesign.E.IsCylDecompOn n A C → ∀ κ ∈ C, κ.Nonempty) :=
  ⟨isPreconnected_of_isCell, isPreconnected_cubeC, isCylDecompOn_subset, isCylDecompOn_sUnion,
   isCylDecompOn_nonempty⟩

end Work.WilE7

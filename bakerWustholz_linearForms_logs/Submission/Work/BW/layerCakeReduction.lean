import Mathlib
import Submission.Work.BW.lcDefs
import Submission.Work.BW.piFubini
import Submission.Work.BW.bwSet_convex
import Submission.Work.BW.bwSet_neg
import Submission.Work.BW.bwSet_slice
import Submission.Work.BW.measurableSet_bwSet
import Submission.Work.BW.lcJoint_aemeasurable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ## Elementary layer-cake facts -/

lemma lintegral_indicator_one' {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) :
    (∫⁻ a, Set.indicator s (fun _ => (1 : ℝ≥0∞)) a ∂μ) = μ s := by
  rw [lintegral_indicator hs (f := fun _ => (1 : ℝ≥0∞))]
  rw [show (∫⁻ a in s, (fun _ => (1 : ℝ≥0∞)) a ∂μ) = (∫⁻ _ in s, (1 : ℝ≥0∞) ∂μ) from by
    apply lintegral_congr
    intro a
    rfl]
  rw [setLIntegral_const, one_mul]

lemma lcInd_integral (c : ℝ) : ∫⁻ u : ℝ, lcInd c u = ENNReal.ofReal c := by
  have h1 : (∫⁻ u : ℝ, lcInd c u)
      = ∫⁻ u : ℝ, (Set.Icc 0 c).indicator (fun _ => (1 : ℝ≥0∞)) u := by
    apply lintegral_congr; intro u; simp [lcInd]
  rw [h1, lintegral_indicator_one' measurableSet_Icc, Real.volume_Icc, sub_zero]

lemma lcWeight_eq_ofReal {n : ℕ} (h : Fin n → ℝ → ℝ) (hh_nn : ∀ i x, 0 ≤ h i x)
    (y : Fin n → ℝ) : lcWeight h y = ENNReal.ofReal (∏ i, h i (y i)) := by
  rw [lcWeight, ENNReal.ofReal_prod_of_nonneg (fun i _ => hh_nn i (y i))]

lemma lcWeight_integral {n : ℕ} (h : Fin n → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i))
    (y : Fin n → ℝ) :
    lcWeight h y = ∫⁻ u : Fin n → ℝ, ∏ i, lcInd (h i (y i)) (u i) := by
  simp only [lcWeight]
  have key : (∫⁻ u : Fin n → ℝ, ∏ i, lcInd (h i (y i)) (u i))
      = ∏ i, ∫⁻ t : ℝ, lcInd (h i (y i)) t := by
    simp only [volume_pi]
    exact lintegral_fin_nat_prod_eq_prod (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun i t => lcInd (h i (y i)) t) (fun i => (measurable_lcInd_left _).aemeasurable)
  rw [key]
  simp only [lcInd_integral]

lemma lcWeight_lintegral {n : ℕ} (h : Fin n → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i))
    (hh_nn : ∀ i x, 0 ≤ h i x) (hh_int : ∀ i, Integrable (h i)) :
    (∫⁻ y : Fin n → ℝ, lcWeight h y) = ENNReal.ofReal (∏ i, ∫ t : ℝ, h i t) := by
  have key : (∫⁻ y : Fin n → ℝ, lcWeight h y)
      = ∏ i, ∫⁻ t : ℝ, ENNReal.ofReal (h i t) := by
    simp only [lcWeight]
    simp only [volume_pi]
    exact lintegral_fin_nat_prod_eq_prod (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun i t => ENNReal.ofReal (h i t))
      (fun i => (ENNReal.measurable_ofReal.comp (hh_meas i)).aemeasurable)
  rw [key]
  rw [show (∏ i, ∫⁻ t : ℝ, ENNReal.ofReal (h i t))
        = ∏ i, ENNReal.ofReal (∫ t : ℝ, h i t) from by
      apply Finset.prod_congr rfl
      intro i _
      exact (ofReal_integral_eq_lintegral_ofReal (hh_int i) (ae_of_all _ (hh_nn i))).symm]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun t => hh_nn i t))]

/-! ## Pointwise identities -/

lemma indicator_one_eq_ofReal {α : Type*} (s : Set α) (y : α) :
    Set.indicator s (fun _ => (1 : ℝ≥0∞)) y
      = ENNReal.ofReal (Set.indicator s (fun _ => (1 : ℝ)) y) := by
  by_cases h : y ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma indicator_one_mul_eq {α : Type*} (s : Set α) (g : α → ℝ) (y : α) :
    Set.indicator s (fun _ => (1 : ℝ)) y * g y = Set.indicator s g y := by
  by_cases h : y ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma indicator_one_mul_enn {α : Type*} (s : Set α) (g : α → ℝ) (y : α) :
    Set.indicator s (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal (g y)
      = ENNReal.ofReal (Set.indicator s g y) := by
  have h0 : 0 ≤ Set.indicator s (fun _ => (1 : ℝ)) y := by
    by_cases h : y ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  rw [indicator_one_eq_ofReal, ← ENNReal.ofReal_mul h0, indicator_one_mul_eq]

lemma indicator_one_mul_indicator_one {α : Type*} (s t : Set α) (y : α) :
    Set.indicator s (fun _ => (1 : ℝ≥0∞)) y * Set.indicator t (fun _ => (1 : ℝ≥0∞)) y
      = Set.indicator (s ∩ t) (fun _ => (1 : ℝ≥0∞)) y := by
  by_cases hs : y ∈ s <;> by_cases ht : y ∈ t <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs, ht]

lemma prod_lcInd_eq_indicator {n : ℕ} (h : Fin n → ℝ → ℝ) (u y : Fin n → ℝ) :
    (∏ i, lcInd (h i (y i)) (u i))
      = Set.indicator {y : Fin n → ℝ | ∀ i, 0 ≤ u i ∧ u i ≤ h i (y i)}
          (fun _ => (1 : ℝ≥0∞)) y := by
  have hprod : (∏ i, lcInd (h i (y i)) (u i))
      = if ∀ i, 0 ≤ u i ∧ u i ≤ h i (y i) then (1 : ℝ≥0∞) else 0 := by
    simp only [lcInd_apply]
    rw [Finset.prod_boole]
    simp
  rw [hprod]
  by_cases hP : ∀ i, 0 ≤ u i ∧ u i ≤ h i (y i)
  · rw [if_pos hP, Set.indicator_of_mem
      (show y ∈ {y : Fin n → ℝ | ∀ i, 0 ≤ u i ∧ u i ≤ h i (y i)} from hP)]
  · rw [if_neg hP, Set.indicator_of_notMem
      (show y ∉ {y : Fin n → ℝ | ∀ i, 0 ≤ u i ∧ u i ≤ h i (y i)} from hP)]

lemma lcJoint_eq_indicator {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (h : Fin n → ℝ → ℝ) (s : ℝ) (u y : Fin n → ℝ) :
    lcJoint C k h s y u
      = Set.indicator {y : Fin n → ℝ | Fin.insertNth k s y ∈ bwSet C k h u}
          (fun _ => (1 : ℝ≥0∞)) y := by
  have hT : {y : Fin n → ℝ | Fin.insertNth k s y ∈ C}
        ∩ {y : Fin n → ℝ | ∀ i, 0 ≤ u i ∧ u i ≤ h i (y i)}
      = {y : Fin n → ℝ | Fin.insertNth k s y ∈ bwSet C k h u} := by
    rw [bwSet_slice C k h s u]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [lcJoint, prod_lcInd_eq_indicator, indicator_one_mul_indicator_one, hT]

lemma lcJoint_integral {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (h : Fin n → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i)) (hcl : IsClosed C) (s : ℝ)
    (u : Fin n → ℝ) :
    ∫⁻ y : Fin n → ℝ, lcJoint C k h s y u
      = (volume : Measure (Fin n → ℝ)) {y : Fin n → ℝ | Fin.insertNth k s y ∈ bwSet C k h u} := by
  have hT : MeasurableSet {y : Fin n → ℝ | Fin.insertNth k s y ∈ bwSet C k h u} :=
    (measurableSet_bwSet C k h hh_meas hcl u).preimage (continuous_insertNth k s).measurable
  rw [show (∫⁻ y : Fin n → ℝ, lcJoint C k h s y u)
        = ∫⁻ y : Fin n → ℝ,
            Set.indicator {y : Fin n → ℝ | Fin.insertNth k s y ∈ bwSet C k h u}
              (fun _ => (1 : ℝ≥0∞)) y from by
      apply lintegral_congr; intro y; exact lcJoint_eq_indicator C k h s u y]
  exact lintegral_indicator_one' hT

/-! ## The layer-cake identity for `lcFl` -/

lemma lcJoint_integral_factor {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (h : Fin n → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i)) (s : ℝ) (y : Fin n → ℝ) :
    Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C} (fun _ => (1 : ℝ≥0∞)) y * lcWeight h y
      = ∫⁻ u : Fin n → ℝ, lcJoint C k h s y u := by
  have hne : Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C} (fun _ => (1 : ℝ≥0∞)) y ≠ ∞ := by
    by_cases hh : Fin.insertNth k s y ∈ C <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hh]
  rw [lcWeight_integral h hh_meas y, ← lintegral_const_mul' _ _ hne]
  simp only [lcJoint]

lemma lcFl_eq_vol {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hcl : IsClosed C) (s : ℝ) :
    lcFl C k h s
      = ∫⁻ u : Fin n → ℝ, (volume : Measure (Fin n → ℝ))
          {y : Fin n → ℝ | Fin.insertNth k s y ∈ bwSet C k h u} := by
  rw [lcFl]
  rw [show (∫⁻ y : Fin n → ℝ, Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}
              (fun _ => (1 : ℝ≥0∞)) y * lcWeight h y)
        = ∫⁻ y : Fin n → ℝ, ∫⁻ u : Fin n → ℝ, lcJoint C k h s y u from by
      apply lintegral_congr; intro y; exact lcJoint_integral_factor C k h hh_meas s y]
  rw [lintegral_lintegral_swap (f := fun y u => lcJoint C k h s y u)
    (lcJoint_aemeasurable C k h hh_meas hcl s)]
  apply lintegral_congr
  intro u
  exact lcJoint_integral C k h hh_meas hcl s u

/-! ## Finiteness and the real-valued integral -/

lemma lcFl_ne_top {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nn : ∀ i x, 0 ≤ h i x)
    (hh_int : ∀ i, Integrable (h i)) (s : ℝ) : lcFl C k h s ≠ ⊤ := by
  have hb : lcFl C k h s ≤ ∫⁻ y : Fin n → ℝ, lcWeight h y := by
    rw [lcFl]
    apply lintegral_mono
    intro y
    by_cases hy : Fin.insertNth k s y ∈ C <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  rw [lcWeight_lintegral h hh_meas hh_nn hh_int] at hb
  exact ne_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)

lemma lcFl_toReal {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (hh_nn : ∀ i x, 0 ≤ h i x) (hh_meas : ∀ i, Measurable (h i))
    (hcl : IsClosed C) (s : ℝ) :
    (lcFl C k h s).toReal
      = ∫ y in {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}, ∏ i, h i (y i) := by
  have hR : MeasurableSet {x : Fin n → ℝ | Fin.insertNth k s x ∈ C} :=
    (hcl.preimage (continuous_insertNth k s)).measurableSet
  have hFl : lcFl C k h s
      = ∫⁻ y : Fin n → ℝ, ENNReal.ofReal
          (Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}
            (fun z => ∏ i, h i (z i)) y) := by
    rw [lcFl]
    apply lintegral_congr
    intro y
    rw [lcWeight_eq_ofReal h hh_nn y]
    exact indicator_one_mul_enn {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}
      (fun z => ∏ i, h i (z i)) y
  have hnn : 0 ≤ᵐ[volume] (fun y : Fin n → ℝ =>
      Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}
        (fun z => ∏ i, h i (z i)) y) :=
    ae_of_all _ (fun y => by
      by_cases hy : Fin.insertNth k s y ∈ C <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy,
          Finset.prod_nonneg (fun i _ => hh_nn i (y i))])
  have haes : AEStronglyMeasurable (fun y : Fin n → ℝ =>
      Set.indicator {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}
        (fun z => ∏ i, h i (z i)) y) :=
    (Measurable.indicator
      (Finset.measurable_prod _ (fun i _ => (hh_meas i).comp (measurable_pi_apply i)))
      hR).aestronglyMeasurable
  rw [hFl, ← integral_eq_lintegral_of_nonneg_ae hnn haes]
  exact integral_indicator hR

/-! ## The theorem -/

theorem layerCakeReduction {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (hconv : Convex ℝ C) (hsym : C = -C) (hcl : IsClosed C)
    (h : Fin n → ℝ → ℝ) (hh_even : ∀ i x, h i (-x) = h i x)
    (hh_anti : ∀ i, AntitoneOn (h i) (Set.Ici 0))
    (hh_nn : ∀ i x, 0 ≤ h i x) (hh_meas : ∀ i, Measurable (h i))
    (hh_int : ∀ i, MeasureTheory.Integrable (h i))
    (unweighted : ∀ D : Set (Fin (n+1) → ℝ), Convex ℝ D → D = -D →
      AntitoneOn (fun s : ℝ => (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
        {x | Fin.insertNth k s x ∈ D}) (Set.Ici 0)) :
    AntitoneOn (fun s : ℝ =>
      ∫ y in {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}, ∏ i, h i (y i)) (Set.Ici 0) := by
  have hmono : AntitoneOn (fun s => lcFl C k h s) (Set.Ici 0) := by
    intro a ha b hb hab
    change lcFl C k h b ≤ lcFl C k h a
    rw [lcFl_eq_vol C k h hh_meas hcl a, lcFl_eq_vol C k h hh_meas hcl b]
    apply lintegral_mono
    intro u
    exact (unweighted (bwSet C k h u) (bwSet_convex C k h hh_even hh_anti hconv u)
      (bwSet_neg C k h hh_even hsym u)) ha hb hab
  have hfin : ∀ s ∈ Set.Ici 0, lcFl C k h s ≠ ⊤ :=
    fun s _ => lcFl_ne_top C k h hh_meas hh_nn hh_int s
  have hfuneq : (fun s : ℝ => ∫ y in {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}, ∏ i, h i (y i))
      = fun s => (lcFl C k h s).toReal := by
    funext s
    exact (lcFl_toReal C k h hh_nn hh_meas hcl s).symm
  rw [hfuneq]
  intro a ha b hb hab
  change (lcFl C k h b).toReal ≤ (lcFl C k h a).toReal
  exact ENNReal.toReal_mono (hfin a ha) (hmono ha hb hab)

end

end Work.BW

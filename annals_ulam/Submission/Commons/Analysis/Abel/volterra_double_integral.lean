import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Commons.Analysis.Abel.hasDerivAt_invSqrt_weighted_affine

noncomputable section

open scoped Interval Topology
open Set Filter MeasureTheory

namespace Commons.Analysis.Abel


lemma intervalIntegral_indicator_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : ℝ} (hac : a < c) (hcb : c ≤ b) (f : ℝ → E) :
    ∫ x in a..b, Set.indicator {x | c ≤ x} f x = ∫ x in c..b, f x := by
  have hab : a ≤ b := le_trans (le_of_lt hac) hcb
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcb]
  change ∫ x in Set.Ioc a b, (Set.Ici c).indicator f x ∂volume = ∫ x in Set.Ioc c b, f x ∂volume
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Set.Ioc a b ∩ Set.Ici c = Set.Icc c b := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2, hx.1.2⟩
    · intro hx
      constructor
      · constructor
        · exact lt_of_lt_of_le hac hx.1
        · exact hx.2
      · exact hx.1
  rw [hset]
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (α := ℝ) (μ := volume) (a := c) (b := b)).symm]


lemma intervalIntegrable_invSqrt_sub
    {a b : ℝ} (hab : a < b) :
    IntervalIntegrable (fun x => (Real.sqrt (x - a))⁻¹) volume a b := by
  let g : ℝ → ℝ := fun x => 2 * Real.sqrt (x - a)
  have hcont : ContinuousOn g (Set.uIcc a b) := by
    dsimp [g]
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt g ((Real.sqrt (x - a))⁻¹) x := by
    intro x hx
    have hxne : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.1)
    have hsqrt := Real.hasDerivAt_sqrt hxne
    have hlin : HasDerivAt (fun y : ℝ => y - a) 1 x := (hasDerivAt_id x).sub_const a
    have hcomp : HasDerivAt (fun y : ℝ => Real.sqrt (y - a)) (1 / (2 * Real.sqrt (x - a))) x := by
      simpa [Function.comp_def] using HasDerivAt.comp (x := x) (h := fun y : ℝ => y - a) (h₂ := Real.sqrt)
        (h' := 1) (h₂' := 1 / (2 * Real.sqrt (x - a))) hsqrt hlin
    have hg : HasDerivAt g (2 * (1 / (2 * Real.sqrt (x - a)))) x := by
      dsimp [g]
      exact hcomp.const_mul 2
    have hderiv_val : 2 * (1 / (2 * Real.sqrt (x - a))) = (Real.sqrt (x - a))⁻¹ := by
      field_simp [hxne, (Real.sqrt_pos_of_pos (sub_pos.mpr hx.1)).ne']
    exact hg.congr_deriv hderiv_val
  have hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ (Real.sqrt (x - a))⁻¹ := by
    intro x hx
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hderiv' : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt g ((Real.sqrt (x - a))⁻¹) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := by
      simpa [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)] using hx
    exact hderiv x hx'
  have hpos' : ∀ x ∈ Set.Ioo (min a b) (max a b), 0 ≤ (Real.sqrt (x - a))⁻¹ := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := by
      simpa [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)] using hx
    exact hpos x hx'
  exact intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont hderiv' hpos'

lemma integral_invSqrt_sub
    {a b : ℝ} (hab : a < b) :
    ∫ y in a..b, (Real.sqrt (y - a))⁻¹ = 2 * Real.sqrt (b - a) := by
  let f : ℝ → ℝ := fun y => 2 * Real.sqrt (y - a)
  let f' : ℝ → ℝ := fun y => (Real.sqrt (y - a))⁻¹
  have hcont : ContinuousOn f (Set.Icc a b) := by
    dsimp [f]
    fun_prop
  have hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y := by
    intro y hy
    have hyne : y - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hy.1)
    have hsqrt := Real.hasDerivAt_sqrt hyne
    have hlin : HasDerivAt (fun t : ℝ => t - a) 1 y := (hasDerivAt_id y).sub_const a
    have hcomp : HasDerivAt (fun t : ℝ => Real.sqrt (t - a)) (1 / (2 * Real.sqrt (y - a))) y := by
      simpa [Function.comp_def] using HasDerivAt.comp (x := y) (h := fun t : ℝ => t - a) (h₂ := Real.sqrt)
        (h' := 1) (h₂' := 1 / (2 * Real.sqrt (y - a))) hsqrt hlin
    have hf : HasDerivAt f (2 * (1 / (2 * Real.sqrt (y - a)))) y := by
      dsimp [f]
      exact hcomp.const_mul 2
    have hderiv_val : 2 * (1 / (2 * Real.sqrt (y - a))) = f' y := by
      dsimp [f']
      field_simp [hyne, (Real.sqrt_pos_of_pos (sub_pos.mpr hy.1)).ne']
    exact hf.congr_deriv hderiv_val
  have hint : IntervalIntegrable f' volume a b := by
    simpa [f'] using intervalIntegrable_invSqrt_sub hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hab) hcont hderiv hint
  dsimp [f, f'] at h
  have hb : 2 * Real.sqrt (b - a) - 2 * Real.sqrt (a - a) = 2 * Real.sqrt (b - a) := by
    rw [sub_self, Real.sqrt_zero, mul_zero, sub_zero]
  simpa [f, f'] using h

lemma intervalIntegrable_indicator_ge_const_mul_invSqrt_sub
    {a b x C : ℝ} (hax : a < x) (hxb : x < b) :
    IntervalIntegrable (fun y => if x ≤ y then C * (Real.sqrt (y - x))⁻¹ else 0) volume a b := by
  let F : ℝ → ℝ := fun y => C * (Real.sqrt (y - x))⁻¹
  have hint_F_xb : IntervalIntegrable F volume x b := by
    have h := intervalIntegrable_invSqrt_sub (a:=x) (b:=b) hxb
    simpa [F] using h.const_mul C
  have h_eq_xb : Set.EqOn (fun y => if x ≤ y then F y else 0) F (Set.uIoo x b) := by
    intro y hy
    have hyx : x < y := by
      simpa [min_eq_left (le_of_lt hxb), max_eq_right (le_of_lt hxb)] using hy.1
    simp [F, hyx.le]
  have hint_xb : IntervalIntegrable (fun y => if x ≤ y then F y else 0) volume x b :=
    (intervalIntegrable_congr_uIoo h_eq_xb).2 hint_F_xb
  have h_zero_ax : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume a x := by
    exact intervalIntegrable_const
  have h_eq_ax : Set.EqOn (fun y => if x ≤ y then F y else 0) (fun _ => (0:ℝ)) (Set.uIoo a x) := by
    intro y hy
    have hyx : y < x := by
      simpa [min_eq_left (le_of_lt hax), max_eq_right (le_of_lt hax)] using hy.2
    simp [F, not_le.mpr hyx]
  have hint_ax : IntervalIntegrable (fun y => if x ≤ y then F y else 0) volume a x :=
    (intervalIntegrable_congr_uIoo h_eq_ax).2 h_zero_ax
  exact hint_ax.trans hint_xb

lemma integrableOn_weight_triangle
    {a b : ℝ} (hab : a < b) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.1 - a))⁻¹ * (Real.sqrt (p.2 - p.1))⁻¹ else 0)
      (Set.uIoc a b ×ˢ Set.uIoc a b) := by
  let S : Set ℝ := Set.uIoc a b
  let μ : Measure ℝ := volume.restrict S
  let g : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then
    (Real.sqrt (p.1 - a))⁻¹ * (Real.sqrt (p.2 - p.1))⁻¹ else 0
  have hS_meas : MeasurableSet S := by dsimp [S]; exact measurableSet_uIoc
  have h_ae_Ioo : ∀ᵐ x ∂μ, x ∈ Set.Ioo a b := by
    rw [ae_iff]
    change (volume.restrict S) {x | x ∉ Set.Ioo a b} = 0
    dsimp [S]
    rw [Set.uIoc_of_le (le_of_lt hab)]
    rw [Measure.restrict_apply (s := Set.Ioc a b) (t := {x | x ∉ Set.Ioo a b}) (ht := measurableSet_Ioo.compl)]
    have h_inter : {x : ℝ | x ∉ Set.Ioo a b} ∩ Set.Ioc a b = {b} := by
      ext x
      constructor
      · intro hx
        have hxIoc : x ∈ Set.Ioc a b := hx.2
        have hxnot : x ∉ Set.Ioo a b := hx.1
        have hxle : x ≤ b := hxIoc.2
        have hxa : a < x := hxIoc.1
        by_cases hxb : x = b
        · exact hxb
        · have hxlt : x < b := lt_of_le_of_ne hxle hxb
          have : x ∈ Set.Ioo a b := ⟨hxa, hxlt⟩
          exact False.elim (hxnot this)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        constructor
        · simp
        · rw [Set.mem_Ioc]; exact ⟨hab, le_rfl⟩
    rw [h_inter]
    simp [measure_singleton]
  have hsqrt1 : Measurable (fun p : ℝ × ℝ => Real.sqrt (p.1 - a)) :=
    Real.continuous_sqrt.measurable.comp (measurable_fst.sub measurable_const)
  have hsqrt2 : Measurable (fun p : ℝ × ℝ => Real.sqrt (p.2 - p.1)) :=
    Real.continuous_sqrt.measurable.comp (measurable_snd.sub measurable_fst)
  have hg_measurable : Measurable g := by
    dsimp [g]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      ((Measurable.inv hsqrt1).mul (Measurable.inv hsqrt2)) measurable_const
  have hg_meas : AEStronglyMeasurable g (μ.prod μ) := by
    exact hg_measurable.aestronglyMeasurable
  have h_fib : ∀ᵐ x ∂μ, Integrable (fun y => g (x, y)) μ := by
    filter_upwards [h_ae_Ioo] with x hx
    have hint : IntervalIntegrable (fun y : ℝ => if x ≤ y then
        (Real.sqrt (x - a))⁻¹ * (Real.sqrt (y - x))⁻¹ else 0) volume a b := by
      simpa [mul_assoc] using intervalIntegrable_indicator_ge_const_mul_invSqrt_sub
        (a := a) (b := b) (x := x) (C := (Real.sqrt (x - a))⁻¹) hx.1 hx.2
    have hintOn : IntegrableOn (fun y : ℝ => if x ≤ y then
        (Real.sqrt (x - a))⁻¹ * (Real.sqrt (y - x))⁻¹ else 0) (Set.Ioc a b) := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hab)).mp hint
    dsimp [μ, S]
    rw [Set.uIoc_of_le (le_of_lt hab)]
    simpa [g, MeasureTheory.IntegrableOn, mul_comm, mul_left_comm, mul_assoc] using hintOn
  have h_int_x : Integrable (fun x : ℝ => ∫ y : ℝ, ‖g (x, y)‖ ∂μ) μ := by
    let D : ℝ := 2 * Real.sqrt (b - a)
    have hbound_base : Integrable (fun x : ℝ => D * (Real.sqrt (x - a))⁻¹) μ := by
      have hint := intervalIntegrable_invSqrt_sub hab
      have hintOn : IntegrableOn (fun x : ℝ => D * (Real.sqrt (x - a))⁻¹) (Set.Ioc a b) := by
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hab)).mp
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using hint.const_mul D)
      dsimp [μ, S]
      rw [Set.uIoc_of_le (le_of_lt hab)]
      simpa [MeasureTheory.IntegrableOn, mul_comm, mul_left_comm, mul_assoc] using hintOn
    let F : ℝ → ℝ := fun x => (Real.sqrt (x - a))⁻¹ * (2 * Real.sqrt (b - x))
    have hF_meas : AEStronglyMeasurable F μ := by
      dsimp [F, μ, S]
      fun_prop
    have hF_bound_ae : ∀ᵐ x ∂μ, ‖F x‖ ≤ D * (Real.sqrt (x - a))⁻¹ := by
      filter_upwards [h_ae_Ioo] with x hx
      have hxnonneg : 0 ≤ (Real.sqrt (x - a))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
      have hsqrt_nonneg : 0 ≤ Real.sqrt (b - x) := Real.sqrt_nonneg _
      have hsqrt_le : Real.sqrt (b - x) ≤ Real.sqrt (b - a) := by
        apply Real.sqrt_le_sqrt
        exact sub_le_sub_left (le_of_lt hx.1) b
      have hF_nonneg : 0 ≤ F x := by
        dsimp [F]
        exact mul_nonneg hxnonneg (mul_nonneg h2nonneg hsqrt_nonneg)
      rw [Real.norm_of_nonneg hF_nonneg]
      dsimp [F, D]
      calc
        (Real.sqrt (x - a))⁻¹ * (2 * Real.sqrt (b - x))
            ≤ (Real.sqrt (x - a))⁻¹ * (2 * Real.sqrt (b - a)) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)) hxnonneg
        _ = D * (Real.sqrt (x - a))⁻¹ := by ring
    have hF_int : Integrable F μ := by
      exact MeasureTheory.Integrable.mono' hbound_base hF_meas hF_bound_ae
    have h_eq_inner : (fun x : ℝ => ∫ y : ℝ, ‖g (x, y)‖ ∂μ) =ᵐ[μ] F := by
      filter_upwards [h_ae_Ioo] with x hx
      let f : ℝ → ℝ := fun y => (Real.sqrt (x - a))⁻¹ * (Real.sqrt (y - x))⁻¹
      have h_left : (∫ y : ℝ, ‖g (x, y)‖ ∂μ) = ∫ y in a..b, (Set.Ici x).indicator f y := by
        dsimp [μ, S]
        rw [Set.uIoc_of_le (le_of_lt hab)]
        rw [intervalIntegral.integral_of_le (le_of_lt hab)]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro y hy
        by_cases hxy : x ≤ y
        · have hnonneg : 0 ≤ (Real.sqrt (x - a))⁻¹ * (Real.sqrt (y - x))⁻¹ := by
            exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
          simp only [g, f, Set.indicator, hxy, Set.mem_Ici, if_true, if_false]
          rw [abs_of_nonneg hnonneg]
        · have hzero_nonneg : 0 ≤ (0 : ℝ) := le_rfl
          simp only [g, f, Set.indicator, hxy, Set.mem_Ici, if_true, if_false]
          rw [abs_of_nonneg hzero_nonneg]
      have h_ind := intervalIntegral_indicator_ge (a := a) (b := b) (c := x) (hac := hx.1) (hcb := le_of_lt hx.2) f
      have h_pull : (∫ y in x..b, f y) = (Real.sqrt (x - a))⁻¹ * (∫ y in x..b, (Real.sqrt (y - x))⁻¹) := by
        simp [f, intervalIntegral.integral_const_mul]
      have h_inv := integral_invSqrt_sub (a := x) (b := b) hx.2
      calc
        ∫ y : ℝ, ‖g (x, y)‖ ∂μ = ∫ y in a..b, (Set.Ici x).indicator f y := h_left
        _ = ∫ y in x..b, f y := h_ind
        _ = (Real.sqrt (x - a))⁻¹ * (∫ y in x..b, (Real.sqrt (y - x))⁻¹) := h_pull
        _ = (Real.sqrt (x - a))⁻¹ * (2 * Real.sqrt (b - x)) := by rw [h_inv]
        _ = F x := by rfl
    exact MeasureTheory.Integrable.congr hF_int h_eq_inner.symm
  have h_prod : Integrable g (μ.prod μ) := by
    exact (MeasureTheory.integrable_prod_iff (μ := μ) (ν := μ) hg_meas).2 ⟨h_fib, h_int_x⟩
  have h_on : IntegrableOn g (S ×ˢ S) := by
    change Integrable g ((volume.prod volume).restrict (S ×ˢ S))
    rw [← MeasureTheory.Measure.prod_restrict]
    exact h_prod
  simpa [g, S] using h_on



lemma integrableOn_invSqrt_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b)) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ =>
        if p.1 ≤ p.2 then
          (Real.sqrt (p.1 - a))⁻¹ • (Real.sqrt (p.2 - p.1))⁻¹ • K p.1 p.2
        else 0)
      (Set.uIoc a b ×ˢ Set.uIoc a b) := by
  let S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc a b
  let t : Set (ℝ × ℝ) := Set.uIoc a b ×ˢ Set.uIoc a b
  have hK_cont_norm : ContinuousOn (fun p : ℝ × ℝ => ‖K p.1 p.2‖) S := hK_cont.norm
  have hS_compact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hS_compact.exists_bound_of_continuousOn hK_cont_norm
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
  have hC_bound : ∀ p ∈ S, ‖K p.1 p.2‖ ≤ C := by
    intro p hp
    exact le_trans (by simpa using hC0 p hp) (by dsimp [C]; exact le_max_left _ _)
  have hweight := integrableOn_weight_triangle hab
  have hweightC : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then C * ((Real.sqrt (p.1 - a))⁻¹ * (Real.sqrt (p.2 - p.1))⁻¹) else 0)
      t := by
    simpa [t, MeasureTheory.IntegrableOn, mul_assoc] using hweight.const_mul C
  let w1 : ℝ × ℝ → ℝ := fun p => (Real.sqrt (p.1 - a))⁻¹
  let w2 : ℝ × ℝ → ℝ := fun p => (Real.sqrt (p.2 - p.1))⁻¹
  let Kcurry : ℝ × ℝ → E := fun p => K p.1 p.2
  let H : ℝ × ℝ → E := fun p => (w1 p * w2 p) • Kcurry p
  let F : ℝ × ℝ → E := fun p => if p.1 ≤ p.2 then H p else 0
  have ht_meas : MeasurableSet t := measurableSet_uIoc.prod measurableSet_uIoc
  have hts : t ⊆ S := by
    intro p hp
    have hp' : p.1 ∈ Set.Ioc a b ∧ p.2 ∈ Set.Ioc a b := by
      simpa [t, Set.uIoc_of_le (le_of_lt hab)] using hp
    exact ⟨⟨le_of_lt hp'.1.1, hp'.1.2⟩, ⟨le_of_lt hp'.2.1, hp'.2.2⟩⟩
  have hK_ae : AEStronglyMeasurable Kcurry (volume.restrict t) := by
    dsimp [Kcurry]
    exact hK_cont.aestronglyMeasurable_of_subset_isCompact hS_compact ht_meas hts
  have hw1_meas : Measurable w1 := by
    dsimp [w1]
    exact Measurable.inv (Real.continuous_sqrt.measurable.comp (measurable_fst.sub measurable_const))
  have hw2_meas : Measurable w2 := by
    dsimp [w2]
    exact Measurable.inv (Real.continuous_sqrt.measurable.comp (measurable_snd.sub measurable_fst))
  have hw_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => w1 p * w2 p) (volume.restrict t) :=
    (hw1_meas.mul hw2_meas).aestronglyMeasurable
  have hH_ae : AEStronglyMeasurable H (volume.restrict t) := by
    dsimp [H]
    exact hw_ae.smul hK_ae
  have hcond_meas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hF_ae : AEStronglyMeasurable F (volume.restrict t) := by
    dsimp [F]
    exact hH_ae.indicator hcond_meas
  have hle_ae : ∀ᵐ p ∂(volume.restrict t), ‖F p‖ ≤
      (if p.1 ≤ p.2 then C * (w1 p * w2 p) else 0) := by
    filter_upwards [ae_restrict_mem ht_meas] with p hp
    by_cases hle : p.1 ≤ p.2
    · have hpS : p ∈ S := hts hp
      have hK_norm : ‖Kcurry p‖ ≤ C := by simpa [Kcurry] using hC_bound p hpS
      have hw_nonneg : 0 ≤ w1 p * w2 p := by
        dsimp [w1, w2]
        exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
      dsimp [F, H]
      rw [if_pos hle, if_pos hle]
      calc
        ‖(w1 p * w2 p) • Kcurry p‖ = |w1 p * w2 p| * ‖Kcurry p‖ := norm_smul _ _
        _ = (w1 p * w2 p) * ‖Kcurry p‖ := by rw [abs_of_nonneg hw_nonneg]
        _ ≤ (w1 p * w2 p) * C := mul_le_mul_of_nonneg_left hK_norm hw_nonneg
        _ = C * (w1 p * w2 p) := mul_comm _ _
    · dsimp [F, H]
      rw [if_neg hle, if_neg hle]
      exact norm_zero.le
  have hF_int_restrict : Integrable F (volume.restrict t) := by
    apply MeasureTheory.Integrable.mono' hweightC hF_ae ?_
    filter_upwards [ae_restrict_mem ht_meas] with p hp
    by_cases hle : p.1 ≤ p.2
    · have hpS : p ∈ S := hts hp
      have hK_norm : ‖Kcurry p‖ ≤ C := by simpa [Kcurry] using hC_bound p hpS
      have hw_nonneg : 0 ≤ w1 p * w2 p := by
        dsimp [w1, w2]
        exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
      dsimp [F, H]
      rw [if_pos hle, if_pos hle]
      calc
        ‖(w1 p * w2 p) • Kcurry p‖ = |w1 p * w2 p| * ‖Kcurry p‖ := norm_smul _ _
        _ = (w1 p * w2 p) * ‖Kcurry p‖ := by rw [abs_of_nonneg hw_nonneg]
        _ ≤ (w1 p * w2 p) * C := mul_le_mul_of_nonneg_left hK_norm hw_nonneg
        _ = C * (w1 p * w2 p) := mul_comm _ _
    · dsimp [F, H]
      rw [if_neg hle, if_neg hle]
      simp
  simpa [F, H, w1, w2, Kcurry, t, MeasureTheory.IntegrableOn, smul_smul] using hF_int_restrict



lemma intervalIntegral_triangle_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a ≤ b)
    {F : ℝ → ℝ → E}
    (hF_int : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then F p.1 p.2 else 0)
      (Set.uIoc a b ×ˢ Set.uIoc a b)) :
    (∫ σ in a..b, ∫ x in a..σ, F x σ) =
      ∫ x in a..b, ∫ σ in x..b, F x σ := by
  let G : ℝ → ℝ → E := fun x σ => if x ≤ σ then F x σ else 0
  have hswap_int : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => G p.2 p.1)
      (Set.uIoc a b ×ˢ Set.uIoc a b) := by
    dsimp [G]
    change MeasureTheory.Integrable
      (fun p : ℝ × ℝ => if p.2 ≤ p.1 then F p.2 p.1 else 0)
      (volume.restrict (Set.uIoc a b ×ˢ Set.uIoc a b))
    change MeasureTheory.Integrable
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then F p.1 p.2 else 0)
      (volume.restrict (Set.uIoc a b ×ˢ Set.uIoc a b)) at hF_int
    change MeasureTheory.Integrable
      (fun p : ℝ × ℝ => if p.2 ≤ p.1 then F p.2 p.1 else 0)
      ((volume.prod volume).restrict (Set.uIoc a b ×ˢ Set.uIoc a b))
    change MeasureTheory.Integrable
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then F p.1 p.2 else 0)
      ((volume.prod volume).restrict (Set.uIoc a b ×ˢ Set.uIoc a b)) at hF_int
    rw [← MeasureTheory.Measure.prod_restrict] at hF_int ⊢
    exact (MeasureTheory.integrable_swap_iff (μ := volume.restrict (Set.uIoc a b))
      (ν := volume.restrict (Set.uIoc a b))).2 hF_int
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := fun σ x => G x σ) (a := a) (b := b) (c := a) (d := b) hswap_int
  have hinner_left : ∀ σ ∈ Set.Ioo a b,
      (∫ x in a..b, G x σ) = ∫ x in a..σ, F x σ := by
    intro σ hσ
    have hσcc : σ ∈ Set.Icc a b := ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
    have hind := intervalIntegral.integral_indicator
      (a₁ := a) (a₂ := σ) (a₃ := b) (h := hσcc) (f := fun x => F x σ) (μ := volume)
    simpa [G, Set.indicator] using hind
  have hinner_right : ∀ x ∈ Set.Ioo a b,
      (∫ σ in a..b, G x σ) = ∫ σ in x..b, F x σ := by
    intro x hx
    have hxcc : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hind := intervalIntegral_indicator_ge
      (a := a) (b := b) (c := x) (hac := hx.1) (hcb := le_of_lt hx.2) (f := fun σ => F x σ)
    simpa [G, Set.indicator] using hind
  have hleft : (∫ σ in a..b, ∫ x in a..b, G x σ) =
      ∫ σ in a..b, ∫ x in a..σ, F x σ := by
    exact intervalIntegral.integral_congr_Ioo_of_le hab (fun σ hσ => hinner_left σ hσ)
  have hright : (∫ x in a..b, ∫ σ in a..b, G x σ) =
      ∫ x in a..b, ∫ σ in x..b, F x σ := by
    exact intervalIntegral.integral_congr_Ioo_of_le hab (fun x hx => hinner_right x hx)
  calc
    (∫ σ in a..b, ∫ x in a..σ, F x σ) = ∫ σ in a..b, ∫ x in a..b, G x σ := hleft.symm
    _ = ∫ x in a..b, ∫ σ in a..b, G x σ := hswap
    _ = ∫ x in a..b, ∫ σ in x..b, F x σ := hright



lemma inner_substitution_invSqrt_weight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s σ : ℝ} (hsσ : s < σ)
    (K : ℝ → E) :
    ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (s + τ * (σ - s)) =
      ∫ x in s..σ,
        (Real.sqrt (x - s))⁻¹ • (Real.sqrt (σ - x))⁻¹ • K x := by
  let c : ℝ := σ - s
  let w : ℝ → ℝ := fun t => (Real.sqrt (t * (1 - t)))⁻¹
  let F : ℝ → E := fun y => w ((y - s) / c) • K y
  have hcpos : 0 < c := by dsimp [c]; exact sub_pos.mpr hsσ
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hF_eq : (fun τ : ℝ => w τ • K (s + τ * c)) = fun τ : ℝ => F (s + c * τ) := by
    funext τ
    have harg : (s + c * τ - s) / c = τ := by
      field_simp [hcne]
      ring
    have hKarg : s + τ * c = s + c * τ := by ring
    dsimp [F, w]
    rw [harg, hKarg]
  have hsub0 := intervalIntegral.integral_comp_add_mul (f := F) (a := (0:ℝ)) (b := (1:ℝ)) (c := c) (d := s) hcne
  have hsub : (∫ τ in (0:ℝ)..(1:ℝ), F (s + c * τ)) =
      c⁻¹ • ∫ x in s..σ, F x := by
    simpa [c] using hsub0
  have hsmul : c⁻¹ • (∫ x in s..σ, F x) = ∫ x in s..σ, c⁻¹ • F x := by
    rw [intervalIntegral.integral_smul]
  have hpoint : ∀ x ∈ Set.Ioo s σ,
      c⁻¹ • F x = (Real.sqrt (x - s))⁻¹ • (Real.sqrt (σ - x))⁻¹ • K x := by
    intro x hx
    have hx1 : s < x := hx.1
    have hx2 : x < σ := hx.2
    have hu_pos : 0 < x - s := sub_pos.mpr hx1
    have hv_pos : 0 < σ - x := sub_pos.mpr hx2
    have hprod : ((x - s) / c) * (1 - (x - s) / c) = ((x - s) * (σ - x)) / (c * c) := by
      dsimp [c]
      field_simp [sub_ne_zero.mpr (ne_of_gt hsσ)]
      ring
    have hsqrt_prod : Real.sqrt (((x - s) / c) * (1 - (x - s) / c))
        = Real.sqrt ((x - s) * (σ - x)) / c := by
      rw [hprod]
      rw [Real.sqrt_div (mul_nonneg (le_of_lt hu_pos) (le_of_lt hv_pos)) (c * c)]
      have hsqrt_cc : Real.sqrt (c * c) = c := by
        rw [Real.sqrt_mul (le_of_lt hcpos) c]
        rw [← sq]
        exact Real.sq_sqrt (le_of_lt hcpos)
      rw [hsqrt_cc]
    have hscalar : c⁻¹ * w ((x - s) / c) =
        (Real.sqrt (x - s))⁻¹ * (Real.sqrt (σ - x))⁻¹ := by
      dsimp [w]
      rw [hsqrt_prod]
      have hden : Real.sqrt ((x - s) * (σ - x)) =
          Real.sqrt (x - s) * Real.sqrt (σ - x) := by
        rw [Real.sqrt_mul (le_of_lt hu_pos) (σ - x)]
      rw [hden]
      have hsqrt_pos : 0 < Real.sqrt (x - s) * Real.sqrt (σ - x) := by
        exact mul_pos (Real.sqrt_pos_of_pos hu_pos) (Real.sqrt_pos_of_pos hv_pos)
      field_simp [hcne, hsqrt_pos.ne']
    calc
      c⁻¹ • F x = c⁻¹ • (w ((x - s) / c) • K x) := by rfl
      _ = (c⁻¹ * w ((x - s) / c)) • K x := by rw [smul_smul]
      _ = ((Real.sqrt (x - s))⁻¹ * (Real.sqrt (σ - x))⁻¹) • K x := by rw [hscalar]
      _ = (Real.sqrt (x - s))⁻¹ • (Real.sqrt (σ - x))⁻¹ • K x := by rw [smul_smul]
  have hcongr : (∫ x in s..σ, c⁻¹ • F x) =
      ∫ x in s..σ, (Real.sqrt (x - s))⁻¹ • (Real.sqrt (σ - x))⁻¹ • K x := by
    apply intervalIntegral.integral_congr_Ioo_of_le (show s ≤ σ by linarith)
    intro x hx
    exact hpoint x hx
  calc
    ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (s + τ * (σ - s))
        = ∫ τ in (0 : ℝ)..(1 : ℝ), w τ • K (s + τ * c) := by
            simp [w, c]
    _ = ∫ τ in (0 : ℝ)..(1 : ℝ), F (s + c * τ) := by
            exact intervalIntegral.integral_congr (by
              intro x hx; exact congrFun hF_eq x)
    _ = c⁻¹ • ∫ x in s..σ, F x := hsub
    _ = ∫ x in s..σ, c⁻¹ • F x := hsmul
    _ = ∫ x in s..σ, (Real.sqrt (x - s))⁻¹ • (Real.sqrt (σ - x))⁻¹ • K x := hcongr



/-- The iterated-integral identity for the weighted Abel/Volterra transform. -/
lemma volterra_double_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b)) :
    ∀ s ∈ Set.Ioo a b,
      (∫ σ in s..b, ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (s + τ * (σ - s)) σ) =
      ∫ x in s..b, (Real.sqrt (x - s))⁻¹ •
        (∫ σ in x..b, (Real.sqrt (σ - x))⁻¹ • K x σ) := by
  intro s hs
  let F : ℝ → ℝ → E := fun x σ =>
    (Real.sqrt (x - s))⁻¹ • (Real.sqrt (σ - x))⁻¹ • K x σ
  have hK_sub : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc s b ×ˢ Set.Icc s b) := by
    exact hK_cont.mono (by
      intro p hp
      exact ⟨⟨le_trans (le_of_lt hs.1) hp.1.1, hp.1.2⟩,
        ⟨le_trans (le_of_lt hs.1) hp.2.1, hp.2.2⟩⟩)
  have hF_int : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then F p.1 p.2 else 0)
      (Set.uIoc s b ×ˢ Set.uIoc s b) := by
    simpa [F] using integrableOn_invSqrt_triangle (a := s) (b := b) hs.2 hK_sub
  have hinner_eq : ∀ σ ∈ Set.Ioo s b,
      (∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (s + τ * (σ - s)) σ) =
        ∫ x in s..σ, F x σ := by
    intro σ hσ
    have hsub := inner_substitution_invSqrt_weight (s := s) (σ := σ) hσ.1 (K := fun x => K x σ)
    simpa [F] using hsub
  have hleft : (∫ σ in s..b, ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (s + τ * (σ - s)) σ) =
      ∫ σ in s..b, ∫ x in s..σ, F x σ := by
    apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2)
    intro σ hσ
    exact hinner_eq σ hσ
  have hswap := intervalIntegral_triangle_swap (a := s) (b := b) (hab := le_of_lt hs.2)
    (F := F) hF_int
  have hright : (∫ x in s..b, ∫ σ in x..b, F x σ) =
      ∫ x in s..b, (Real.sqrt (x - s))⁻¹ •
        (∫ σ in x..b, (Real.sqrt (σ - x))⁻¹ • K x σ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2)
    intro x hx
    dsimp [F]
    rw [intervalIntegral.integral_smul]
  calc
    (∫ σ in s..b, ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (s + τ * (σ - s)) σ)
        = ∫ σ in s..b, ∫ x in s..σ, F x σ := hleft
    _ = ∫ x in s..b, ∫ σ in x..b, F x σ := hswap
    _ = ∫ x in s..b, (Real.sqrt (x - s))⁻¹ •
        (∫ σ in x..b, (Real.sqrt (σ - x))⁻¹ • K x σ) := hright


end Commons.Analysis.Abel
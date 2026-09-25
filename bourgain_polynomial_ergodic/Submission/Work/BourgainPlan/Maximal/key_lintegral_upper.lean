import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_q_strong_p_top

namespace Work.BourgainPlan.Maximal

open MeasureTheory Measure Filter Set
open scoped ENNReal

private lemma indicator_cross_upper {α : Type*} (W F : α → ℝ≥0∞) (c : ℝ) (x : α) (t : ℝ) :
    Set.indicator {y : α | W y ≤ ENNReal.ofReal (t / (2*c))} F x
      = Set.indicator {t' : ℝ | W x ≤ ENNReal.ofReal (t' / (2*c))} (fun _ => (1:ℝ≥0∞)) t * F x := by
  by_cases h : W x ≤ ENNReal.ofReal (t / (2*c))
  · rw [Set.indicator_of_mem (show x ∈ {y : α | W y ≤ ENNReal.ofReal (t / (2*c))} from h),
        Set.indicator_of_mem (show t ∈ {t' : ℝ | W x ≤ ENNReal.ofReal (t' / (2*c))} from h),
        one_mul]
  · rw [Set.indicator_of_notMem (show x ∉ {y : α | W y ≤ ENNReal.ofReal (t / (2*c))} from h),
        Set.indicator_of_notMem (show t ∉ {t' : ℝ | W x ≤ ENNReal.ofReal (t' / (2*c))} from h),
        zero_mul]

private lemma swap_lintegral_rpow_upper {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {W F : α → ℝ≥0∞} (hW : Measurable W) (hF : Measurable F) {c : ℝ}
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        f t * (∫⁻ x, Set.indicator {x : α | W x ≤ ENNReal.ofReal (t / (2*c))} F x ∂μ)
      = ∫⁻ x, F x * (∫⁻ t in Set.Ioi (0:ℝ), f t *
          Set.indicator {t : ℝ | W x ≤ ENNReal.ofReal (t / (2*c))} (fun _ => (1:ℝ≥0∞)) t) ∂μ := by
  have hstep1 : ∫⁻ t in Set.Ioi (0:ℝ),
        f t * (∫⁻ x, Set.indicator {x : α | W x ≤ ENNReal.ofReal (t / (2*c))} F x ∂μ)
      = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ x,
          f t * Set.indicator {x : α | W x ≤ ENNReal.ofReal (t / (2*c))} F x ∂μ := by
    apply lintegral_congr; intro t
    exact (lintegral_const_mul (f t) (hF.indicator (measurableSet_le hW measurable_const))).symm
  rw [hstep1]
  have hjoint : AEMeasurable (Function.uncurry fun t x =>
        f t * Set.indicator {x : α | W x ≤ ENNReal.ofReal (t / (2*c))} F x)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod μ) := by
    refine AEMeasurable.mul (hf.comp measurable_fst).aemeasurable ?_
    refine Measurable.aemeasurable ?_
    refine Measurable.indicator (hF.comp measurable_snd) ?_
    exact measurableSet_le (hW.comp measurable_snd) ((measurable_fst.div_const (2*c)).ennreal_ofReal)
  rw [lintegral_lintegral_swap hjoint]
  apply lintegral_congr; intro x
  calc ∫⁻ t in Set.Ioi (0:ℝ),
        f t * Set.indicator {y : α | W y ≤ ENNReal.ofReal (t / (2*c))} F x
      = ∫⁻ t in Set.Ioi (0:ℝ), f t *
          Set.indicator {t' : ℝ | W x ≤ ENNReal.ofReal (t' / (2*c))} (fun _ => (1:ℝ≥0∞)) t * F x := by
        apply lintegral_congr; intro t
        rw [indicator_cross_upper W F c x t]; ring
    _ = F x * ∫⁻ t in Set.Ioi (0:ℝ), f t *
          Set.indicator {t' : ℝ | W x ≤ ENNReal.ofReal (t' / (2*c))} (fun _ => (1:ℝ≥0∞)) t :=
        (lintegral_mul_const (F x) (hf.mul (((measurable_const (a := (1:ℝ≥0∞))).indicator
          (measurableSet_le measurable_const ((measurable_id.div_const (2*c)).ennreal_ofReal)))))).trans (mul_comm _ _)

private lemma Ici_ae_Ioi (X : ℝ) : Set.Ici X =ᵐ[volume] Set.Ioi X := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (fun t ht => ?_) (by simp : volume ({X} : Set ℝ) = 0)
    obtain ⟨h1, h2⟩ := ht
    simp only [Set.mem_Ici] at h1
    simp only [Set.mem_Ioi] at h2
    simp only [Set.mem_singleton_iff]
    exact le_antisymm (not_lt.mp h2) h1
  · refine measure_mono_null (fun t ht => ?_) measure_empty
    obtain ⟨h1, h2⟩ := ht
    simp only [Set.mem_Ioi] at h1
    simp only [Set.mem_Ici] at h2
    exact absurd h1 (not_lt.mpr (not_le.mp h2).le)

private lemma inner_upper {b c r : ℝ} (hb : 0 < b) (hc : 0 < c) (hr : r < -1) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        Set.indicator {t : ℝ | ENNReal.ofReal b ≤ ENNReal.ofReal (t / (2*c))} (fun _ => (1:ℝ≥0∞)) t
      = ENNReal.ofReal ((2*c*b) ^ (r + 1) / (-(r + 1))) := by
  have h2c : (0:ℝ) < 2*c := by positivity
  have hX : (0:ℝ) < 2*c*b := by positivity
  have hcongr : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        Set.indicator {t : ℝ | ENNReal.ofReal b ≤ ENNReal.ofReal (t / (2*c))} (fun _ => (1:ℝ≥0∞)) t
      = ∫⁻ t in Set.Ioi (0:ℝ),
          Set.indicator (Set.Ici (2*c*b)) (fun t => ENNReal.ofReal (t ^ r)) t := by
    refine lintegral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hiff : (ENNReal.ofReal b ≤ ENNReal.ofReal (t / (2*c))) ↔ b ≤ t / (2*c) :=
      ENNReal.ofReal_le_ofReal_iff (div_nonneg ht.le (by linarith : (0:ℝ) ≤ 2*c))
    have hiff2 : b ≤ t / (2*c) ↔ 2*c*b ≤ t := by
      rw [le_div_iff₀ h2c]; ring_nf
    by_cases hb' : 2*c*b ≤ t
    · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | ENNReal.ofReal b ≤ ENNReal.ofReal (t / (2*c))}
          from hiff.mpr (hiff2.mpr hb')),
        Set.indicator_of_mem (show t ∈ Set.Ici (2*c*b) from hb'), mul_one]
    · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | ENNReal.ofReal b ≤ ENNReal.ofReal (t / (2*c))}
          from fun h => hb' (hiff2.mp (hiff.mp h))),
        Set.indicator_of_notMem (show t ∉ Set.Ici (2*c*b) from fun h => hb' h), mul_zero]
  rw [hcongr,
    Commons.Analysis.MeasureTheory.lintegral_Ioi_indicator_eq measurableSet_Ici
      (fun t ht => lt_of_lt_of_le hX ht),
    Measure.restrict_congr_set (Ici_ae_Ioi (2*c*b)),
    Commons.Analysis.MeasureTheory.lintegral_Ioi_ofReal_rpow (X := 2*c*b) (q := r) hr hX]
  congr 1
  rw [div_neg]

private lemma pointwise_upper {b c q r : ℝ} (hb : 0 ≤ b) (hc : 0 < c) (hq : 0 < q)
    (hqr : 0 < q + r + 1) (hr : r < -1) :
    ENNReal.ofReal b ^ q *
      (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        Set.indicator {t : ℝ | ENNReal.ofReal b ≤ ENNReal.ofReal (t / (2*c))} (fun _ => (1:ℝ≥0∞)) t)
    = ENNReal.ofReal ((2*c) ^ (r + 1) / (-(r + 1))) * ENNReal.ofReal b ^ (q + r + 1) := by
  obtain hb0 | hbpos := eq_or_lt_of_le hb
  · rw [← hb0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq, zero_mul,
      ENNReal.zero_rpow_of_pos hqr, mul_zero]
  · rw [inner_upper hbpos hc hr,
      ENNReal.ofReal_rpow_of_nonneg hb hq.le,
      ENNReal.ofReal_rpow_of_nonneg hb hqr.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hb q),
      ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 2*c) (r+1))
        (by linarith : (0:ℝ) ≤ -(r + 1)))]
    congr 1
    have hreal : b ^ q * ((2*c*b) ^ (r + 1) / (-(r + 1)))
        = (2*c) ^ (r + 1) / (-(r + 1)) * b ^ (q + r + 1) := by
      rw [Real.mul_rpow (by linarith : (0:ℝ) ≤ 2*c) hb]
      rw [show b ^ q * ((2*c) ^ (r + 1) * b ^ (r + 1) / (-(r + 1)))
          = (2*c) ^ (r + 1) / (-(r + 1)) * (b ^ q * b ^ (r + 1)) by ring]
      rw [← Real.rpow_add hbpos q (r + 1), show q + (r + 1) = q + r + 1 by ring]
    exact hreal

/-- The upper level-set version of `key_lintegral`, used for the maximal function. -/
theorem key_lintegral_upper {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ]
    {v : α → ℝ} (hvm : Measurable v) (hv : ∀ x, 0 ≤ v x)
    {c : ℝ} (hc : 0 < c) {q r : ℝ} (hq : 0 < q) (hqr : 0 < q + r + 1) (hr : r < -1) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (v x) ≤ ENNReal.ofReal (t / (2*c))}
            (fun x => ENNReal.ofReal (v x) ^ q) x ∂μ)
      = ENNReal.ofReal ((2*c) ^ (r + 1) / (-(r + 1))) *
          ∫⁻ x, ENNReal.ofReal (v x) ^ (q + r + 1) ∂μ := by
  have hW : Measurable fun x : α => ENNReal.ofReal (v x) := hvm.ennreal_ofReal
  have hF : Measurable fun x : α => ENNReal.ofReal (v x) ^ q :=
    ENNReal.continuous_rpow_const.measurable.comp hW
  have hf : Measurable fun t : ℝ => ENNReal.ofReal (t ^ r) := (Commons.Analysis.MeasureTheory.measurable_rpow_const r).ennreal_ofReal
  rw [swap_lintegral_rpow_upper hW hF hf]
  rw [show (∫⁻ x, ENNReal.ofReal (v x) ^ q *
        (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
          Set.indicator {t : ℝ | ENNReal.ofReal (v x) ≤ ENNReal.ofReal (t / (2*c))}
            (fun _ => (1:ℝ≥0∞)) t) ∂μ)
      = ∫⁻ x, ENNReal.ofReal ((2*c) ^ (r + 1) / (-(r + 1))) * ENNReal.ofReal (v x) ^ (q + r + 1) ∂μ
      from by
        apply lintegral_congr; intro x
        exact pointwise_upper (hv x) hc hq hqr hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Work.BourgainPlan.Maximal

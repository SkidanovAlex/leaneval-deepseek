import Mathlib
import Submission.Commons.Analysis.Fourier.lintegral_translate_sub_sq_le_of_fourier_support

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- Scaling of the Lebesgue `lintegral` on `ℝ` under `t ↦ t * a`, `a ≠ 0`:
`∫⁻ t, φ (t * a) = ofReal |a⁻¹| * ∫⁻ s, φ s`. -/
private lemma lintegral_comp_mul_right_volume (φ : ℝ → ℝ≥0∞) {a : ℝ} (ha : a ≠ 0) :
    ∫⁻ t : ℝ, φ (t * a) = ENNReal.ofReal |a⁻¹| * ∫⁻ s : ℝ, φ s := by
  have h := (measurableEmbedding_mulRight₀ (G₀ := ℝ) ha).lintegral_map
    (μ := (volume : Measure ℝ)) φ
  rw [Real.map_volume_mul_right ha] at h
  rw [← h, lintegral_smul_measure]
  rfl

/-- Pointwise evaluation: for a set `C ⊆ ℝ` the integral `∫ θ, 1_C(θ) e^{-i t θ} dθ` is the
Fourier transform of the indicator of `C`, evaluated at `t / (2π)`. -/
private lemma integral_indicator_exp_eq_fourier (C : Set ℝ) (t : ℝ) :
    (∫ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ)
      = 𝓕 (C.indicator (fun _ => (1 : ℂ))) (t / (2 * Real.pi)) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with θ
  by_cases hθ : θ ∈ C
  · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ]
    simp only [smul_eq_mul, mul_one]
    rw [Real.inner_apply]
    congr 1
    push_cast
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ]
    simp

theorem memLp_itKer_shift (C : Set ℝ) (hC : MeasurableSet C) (hbd : Bornology.IsBounded C)
    (x : ℝ) :
    MeasureTheory.MemLp (fun y : ℝ => ∫ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((x - y : ℝ)) : ℂ) * (θ : ℂ)))) θ)
      2 MeasureTheory.volume := by
  set h : ℝ → ℂ := C.indicator (fun _ => (1 : ℂ)) with hh
  have hfin : (volume : Measure ℝ) C ≠ ∞ :=
    (hbd.measure_lt_top (μ := (volume : Measure ℝ))).ne
  have h1 : MemLp h 1 (volume : Measure ℝ) := by
    rw [hh]; exact memLp_indicator_const 1 hC 1 (Or.inr hfin)
  have h2 : MemLp h 2 (volume : Measure ℝ) := by
    rw [hh]; exact memLp_indicator_const 2 hC 1 (Or.inr hfin)
  have hint : Integrable h := memLp_one_iff_integrable.mp h1
  have hpoint : ∀ y : ℝ, (∫ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((x - y : ℝ)) : ℂ) * (θ : ℂ)))) θ)
      = 𝓕 h ((x - y) / (2 * Real.pi)) := by
    intro y
    rw [hh]
    exact integral_indicator_exp_eq_fourier C (x - y)
  have hcont : Continuous (𝓕 h) := by
    change Continuous (VectorFourier.fourierIntegral (Real.fourierChar) volume (innerₗ ℝ) h)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hint
  have hvol : ∫⁻ s : ℝ, ‖h s‖ₑ ^ (2 : ℝ) = (volume C) := by
    rw [hh]
    have hcongr : ∫⁻ s : ℝ, ‖(C.indicator (fun _ => (1 : ℂ))) s‖ₑ ^ (2 : ℝ)
        = ∫⁻ s : ℝ, C.indicator (fun _ => (1 : ℝ≥0∞)) s := by
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ C
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]; simp
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]; simp
    rw [hcongr]
    exact lintegral_indicator_one hC
  have hψ : ∫⁻ y : ℝ, ‖𝓕 h ((x - y) / (2 * Real.pi))‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal (2 * Real.pi) * (volume C) := by
    have hstep1 : ∫⁻ y : ℝ, ‖𝓕 h ((x - y) / (2 * Real.pi))‖ₑ ^ (2 : ℝ)
        = ∫⁻ u : ℝ, ‖𝓕 h (u / (2 * Real.pi))‖ₑ ^ (2 : ℝ) := by
      have h1' := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun z : ℝ => ‖𝓕 h ((-z) / (2 * Real.pi))‖ₑ ^ (2 : ℝ)) (-x)
      rw [show (fun y : ℝ => ‖𝓕 h ((-(y + -x)) / (2 * Real.pi))‖ₑ ^ (2 : ℝ))
            = (fun y : ℝ => ‖𝓕 h ((x - y) / (2 * Real.pi))‖ₑ ^ (2 : ℝ)) from by
            funext y; rw [show -(y + -x) = x - y by ring]] at h1'
      rw [h1']
      exact lintegral_neg_eq_self (μ := (volume : Measure ℝ))
        (fun z : ℝ => ‖𝓕 h (z / (2 * Real.pi))‖ₑ ^ (2 : ℝ))
    have hstep2 : ∫⁻ u : ℝ, ‖𝓕 h (u / (2 * Real.pi))‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (2 * Real.pi) * ∫⁻ s : ℝ, ‖𝓕 h s‖ₑ ^ (2 : ℝ) := by
      have hadd := lintegral_comp_mul_right_volume (fun s : ℝ => ‖𝓕 h s‖ₑ ^ (2 : ℝ))
        (a := (2 * Real.pi)⁻¹) (inv_ne_zero (by positivity : (2 * Real.pi) ≠ 0))
      rw [inv_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hadd
      rw [← hadd]
      apply lintegral_congr
      intro u
      rw [div_eq_mul_inv]
    calc ∫⁻ y : ℝ, ‖𝓕 h ((x - y) / (2 * Real.pi))‖ₑ ^ (2 : ℝ)
        = ∫⁻ u : ℝ, ‖𝓕 h (u / (2 * Real.pi))‖ₑ ^ (2 : ℝ) := hstep1
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ s : ℝ, ‖𝓕 h s‖ₑ ^ (2 : ℝ) := hstep2
      _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ s : ℝ, ‖h s‖ₑ ^ (2 : ℝ) := by
            rw [lintegral_fourier_sq_eq h1 h2]
      _ = ENNReal.ofReal (2 * Real.pi) * (volume C) := by rw [hvol]
  rw [show (fun y : ℝ => ∫ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((x - y : ℝ)) : ℂ) * (θ : ℂ)))) θ)
      = (fun y : ℝ => 𝓕 h ((x - y) / (2 * Real.pi))) from funext hpoint]
  have hmeas : AEStronglyMeasurable (fun y : ℝ => 𝓕 h ((x - y) / (2 * Real.pi))) volume :=
    (hcont.comp ((continuous_const.sub continuous_id).div_const _)).aestronglyMeasurable
  · rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      hmeas]
    rw [show (2 : ℝ≥0∞).toReal = 2 from ENNReal.toReal_ofNat 2, hψ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hbd.measure_lt_top (μ := (volume : Measure ℝ))).lt_top

end Commons.Analysis.Fourier

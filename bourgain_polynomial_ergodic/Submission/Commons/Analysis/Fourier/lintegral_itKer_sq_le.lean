import Mathlib
import Submission.Commons.Analysis.Fourier.lintegral_fourierInv_eq
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

/-- The `L²` energy of the (unscaled) Fourier transform of the indicator of a bounded measurable
set `C ⊆ ℝ` is at most `2π |C|`.  This is Plancherel's theorem for the pointwise integral
`t ↦ ∫ θ, 1_C(θ) e^{-i t θ} dθ`, combined with the elementary value `∫ |1_C|² = |C|` and the
change of variables `t ↦ t / (2π)` matching the `2π`-convention of Mathlib's Fourier transform. -/
theorem lintegral_itKer_sq_le (C : Set ℝ) (hC : MeasurableSet C) (hbd : Bornology.IsBounded C) :
    ∫⁻ t : ℝ, ‖(∫ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ)‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (2 * Real.pi * (MeasureTheory.volume C).toReal) := by
  set h : ℝ → ℂ := C.indicator (fun _ => (1:ℂ)) with hh
  have hfin : (volume : Measure ℝ) C ≠ ∞ := (hbd.measure_lt_top (μ := (volume : Measure ℝ))).ne
  have h1 : MemLp h 1 (volume : Measure ℝ) := by
    rw [hh]; exact memLp_indicator_const 1 hC 1 (Or.inr hfin)
  have h2 : MemLp h 2 (volume : Measure ℝ) := by
    rw [hh]; exact memLp_indicator_const 2 hC 1 (Or.inr hfin)
  have hpoint : ∀ t : ℝ, (∫ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ)
      = 𝓕 h (t / (2 * Real.pi)) := by
    intro t
    rw [hh]
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
  have hvol : ∫⁻ s : ℝ, ‖h s‖ₑ ^ (2:ℝ) = (volume C) := by
    rw [hh]
    have hcongr : ∫⁻ s : ℝ, ‖(C.indicator (fun _ => (1:ℂ))) s‖ₑ ^ (2:ℝ)
        = ∫⁻ s : ℝ, C.indicator (fun _ => (1:ℝ≥0∞)) s := by
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ C
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]; simp
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]; simp
    rw [hcongr]
    exact lintegral_indicator_one hC
  have hscale : ∫⁻ t : ℝ, ‖𝓕 h (t / (2 * Real.pi))‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ s : ℝ, ‖𝓕 h s‖ₑ ^ (2:ℝ) := by
    have hkey := lintegral_comp_mul_right_volume (fun s : ℝ => ‖𝓕 h s‖ₑ ^ (2:ℝ))
      (a := (2 * Real.pi)⁻¹) (by positivity)
    have hinv : |((2 * Real.pi)⁻¹)⁻¹| = 2 * Real.pi := by
      rw [inv_inv, abs_of_nonneg (by positivity)]
    rw [hinv] at hkey
    simpa only [div_eq_mul_inv] using hkey
  refine le_of_eq ?_
  calc ∫⁻ t : ℝ, ‖(∫ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ)‖ₑ ^ (2:ℝ)
      = ∫⁻ t : ℝ, ‖𝓕 h (t / (2 * Real.pi))‖ₑ ^ (2:ℝ) := by
          apply lintegral_congr; intro t; rw [hpoint t]
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ s : ℝ, ‖𝓕 h s‖ₑ ^ (2:ℝ) := hscale
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ s : ℝ, ‖h s‖ₑ ^ (2:ℝ) := by
          rw [lintegral_fourier_sq_eq h1 h2]
    _ = ENNReal.ofReal (2 * Real.pi) * (volume C) := by rw [hvol]
    _ = ENNReal.ofReal (2 * Real.pi * (MeasureTheory.volume C).toReal) := by
          rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi),
              ENNReal.ofReal_toReal hfin]

end Commons.Analysis.Fourier

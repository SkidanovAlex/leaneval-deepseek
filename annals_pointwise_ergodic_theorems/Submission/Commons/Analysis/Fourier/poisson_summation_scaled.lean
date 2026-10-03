import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Poisson summation, scaled

`∑' n, f (n / N) = N * ∑' m, 𝓕 f (m * N)` for a Schwartz function `f` on `ℝ` and `N > 0`.

This is Poisson summation applied to the dilated function `x ↦ f (x / N)`, together with the
scaling rule for the Fourier transform `𝓕 (fun x ↦ f (x / N)) y = N * 𝓕 f (y * N)`.
-/

namespace Commons.Analysis.Fourier

open MeasureTheory Measure
open scoped FourierTransform

/-- Scaling rule for the Fourier transform on `ℝ`: dilating the argument by a positive factor
`N` scales the Fourier transform by `N` in the dual variable. -/
lemma fourier_comp_div (f : ℝ → ℂ) {N : ℝ} (hN : 0 < N) (y : ℝ) :
    𝓕 (fun x : ℝ => f (x / N)) y = (N : ℂ) * 𝓕 f (y * N) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  let g : ℝ → ℂ := fun z => Real.fourierChar (-(z * (y * N))) • f z
  have h1 : (∫ x : ℝ, Real.fourierChar (-(x * y)) • f (x / N)) = ∫ x, g (x / N) := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [g]
    rw [show x / N * (y * N) = x * y by field_simp]
  rw [h1, integral_comp_div g N, abs_of_pos hN, Complex.real_smul]

theorem poisson_summation_scaled (f : SchwartzMap ℝ ℂ) (N : ℝ) (hN : 0 < N) :
    ∑' n : ℤ, f ((n : ℝ) / N)
      = N * (∑' m : ℤ, FourierTransform.fourier f ((m : ℝ) * N)) := by
  let u : ℝˣ := Units.mk0 N⁻¹ (inv_ne_zero hN.ne')
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ u
  let g : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg : ⇑g = fun x : ℝ => f (x / N) := by
    funext x
    simp only [g, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply]
    rw [Units.val_mk0, div_eq_mul_inv]
  calc ∑' n : ℤ, f ((n : ℝ) / N)
      = ∑' n : ℤ, g (0 + (n : ℝ)) := by
        refine tsum_congr fun n => ?_
        rw [hg]
        simp
    _ = ∑' n : ℤ, (𝓕 g) (n : ℝ) * fourier n ((0 : ℝ) : UnitAddCircle) :=
        SchwartzMap.tsum_eq_tsum_fourier g 0
    _ = ∑' n : ℤ, (N : ℂ) * (𝓕 (f : ℝ → ℂ)) ((n : ℝ) * N) := by
        refine tsum_congr fun n => ?_
        conv_lhs => rw [SchwartzMap.fourier_coe, hg]
        rw [fourier_comp_div (f : ℝ → ℂ) hN]
        simp
    _ = (N : ℂ) * ∑' n : ℤ, (𝓕 (f : ℝ → ℂ)) ((n : ℝ) * N) := tsum_mul_left
    _ = N * (∑' m : ℤ, FourierTransform.fourier f ((m : ℝ) * N)) := rfl

end Commons.Analysis.Fourier
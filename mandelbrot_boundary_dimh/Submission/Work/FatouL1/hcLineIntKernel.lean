import Mathlib

open MeasureTheory

namespace Work.FatouL1

/-- Bound for the Cauchy line integral of `h` against the kernel `1 / (w - z)` along the vertical
line `Re w = L`: the integral is dominated by the (absolute) line integral of `h` against
`1 / sqrt (δ ^ 2 + (y - z.im) ^ 2)`, whenever `0 < δ ≤ |L - z.re|`.

The point is that on the line `w = L + iy` one has
`‖w - z‖ ^ 2 = (L - z.re) ^ 2 + (y - z.im) ^ 2 ≥ δ ^ 2 + (y - z.im) ^ 2`,
so that `1 / ‖w - z‖ ≤ 1 / sqrt (δ ^ 2 + (y - z.im) ^ 2)`. -/
theorem hcLineIntKernel {h : ℂ → ℂ} {L : ℝ} {z : ℂ}
    (hI : MeasureTheory.Integrable (fun y : ℝ => h ((L : ℂ) + y * Complex.I)))
    (hz : L ≠ z.re) {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ |L - z.re|) :
    ‖∫ y : ℝ, h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)‖
      ≤ ∫ y : ℝ, ‖h ((L : ℂ) + y * Complex.I)‖ / Real.sqrt (δ ^ 2 + (y - z.im) ^ 2) := by
  set φ : ℝ → ℝ := fun y => ‖h ((L : ℂ) + y * Complex.I)‖ with hφ
  set G : ℝ → ℝ := fun y => φ y / Real.sqrt (δ ^ 2 + (y - z.im) ^ 2) with hG
  have hφ_nonneg : ∀ y, 0 ≤ φ y := fun y => norm_nonneg _
  have hsq : δ ^ 2 ≤ (L - z.re) ^ 2 := by
    have h := abs_nonneg (L - z.re)
    nlinarith [hδ, hδle, sq_abs (L - z.re), h]
  -- squared modulus of the kernel argument
  have hnorm2 : ∀ y : ℝ,
      ‖((L : ℂ) + (y:ℂ) * Complex.I) - z‖ ^ 2 = (L - z.re)^2 + (y - z.im)^2 := by
    intro y
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, zero_mul, add_zero, sub_zero, mul_one, pow_two]
    ring
  have hsqrt_le : ∀ y : ℝ,
      Real.sqrt (δ ^ 2 + (y - z.im) ^ 2) ≤ ‖((L : ℂ) + (y:ℂ) * Complex.I) - z‖ := by
    intro y
    have h1 : δ ^ 2 + (y - z.im) ^ 2 ≤ ‖((L : ℂ) + (y:ℂ) * Complex.I) - z‖ ^ 2 := by
      rw [hnorm2 y]; linarith [hsq]
    calc Real.sqrt (δ ^ 2 + (y - z.im) ^ 2)
        ≤ Real.sqrt (‖((L : ℂ) + (y:ℂ) * Complex.I) - z‖ ^ 2) := Real.sqrt_le_sqrt h1
      _ = ‖((L : ℂ) + (y:ℂ) * Complex.I) - z‖ := Real.sqrt_sq (norm_nonneg _)
  have hsqrt_pos : ∀ y : ℝ, 0 < Real.sqrt (δ ^ 2 + (y - z.im) ^ 2) := by
    intro y; exact Real.sqrt_pos_of_pos (by nlinarith [hδ])
  -- pointwise domination of the integrand norms
  have hpt : ∀ y : ℝ,
      ‖h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)‖ ≤ G y := by
    intro y
    rw [hG, norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (hsqrt_pos y) (hsqrt_le y)
  have hφ_int : Integrable φ := by rw [hφ]; exact hI.norm
  -- the comparison kernel is integrable, being bounded by `φ / δ`
  have hG_int : Integrable G := by
    refine (hφ_int.div_const δ).mono' ?_ (ae_of_all _ (fun y => ?_))
    · rw [hG]
      have hcont : Continuous (fun y : ℝ => (Real.sqrt (δ ^ 2 + (y - z.im) ^ 2))⁻¹) := by
        refine Continuous.inv₀ ?_ (fun y => ne_of_gt (hsqrt_pos y))
        exact Real.continuous_sqrt.comp (by fun_prop)
      exact hφ_int.aestronglyMeasurable.mul hcont.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg]
      · rw [hG]
        refine div_le_div_of_nonneg_left (hφ_nonneg y) hδ ?_
        rw [Real.le_sqrt (le_of_lt hδ) (by positivity)]
        nlinarith [sq_nonneg (y - z.im)]
      · rw [hG]; exact div_nonneg (hφ_nonneg y) (le_of_lt (hsqrt_pos y))
  calc ‖∫ y : ℝ, h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)‖
      ≤ ∫ y : ℝ, ‖h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, G y :=
        integral_mono_of_nonneg (ae_of_all _ (fun y => norm_nonneg _)) hG_int
          (ae_of_all _ (fun y => hpt y))

end Work.FatouL1

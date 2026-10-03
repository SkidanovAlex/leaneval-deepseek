import Mathlib
import Submission.Work.Fatou.Analysis.norm_sub_le_integral_circle

namespace Work.Fatou.Analysis

open Set Filter Metric MeasureTheory intervalIntegral

/-- Speed (arc-length) estimate in `ℝ≥0∞` for the circle parametrisation
`θ ↦ r * exp (θ * I)`: the displacement of `g` along the arc `[a, b]` is at most the
Lebesgue integral of the speed `r * ‖fderiv ℝ g‖` over `[a, b]`.

Obtained from the Bochner-integral form `norm_sub_le_integral_circle` by lifting the
nonnegative integrand to `ℝ≥0∞` (`ofReal_integral_eq_lintegral_ofReal`). -/
theorem norm_sub_le_lintegral_speed (g : ℂ → ℂ) (r a b : ℝ) (hab : a ≤ b) (hr : 0 ≤ r)
    (hC1 : ContDiff ℝ 1 g) :
    ‖g (r * Complex.exp (b * Complex.I)) - g (r * Complex.exp (a * Complex.I))‖ₑ ≤
      ∫⁻ θ in Set.Icc a b,
        ENNReal.ofReal (r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖) := by
  rw [← ofReal_norm]
  set φ : ℝ → ℝ := fun θ => r * ‖fderiv ℝ g (r * Complex.exp (θ * Complex.I))‖ with hφ
  -- Bochner-integral (speed) form
  have hdisp : ‖g (r * Complex.exp (b * Complex.I)) - g (r * Complex.exp (a * Complex.I))‖ ≤
      ∫ θ in a..b, φ θ := by
    simpa [hφ] using norm_sub_le_integral_circle g r hr a b hab hC1
  -- the integrand is continuous, hence integrable on the compact interval
  have hfdc : Continuous (fderiv ℝ g) := hC1.continuous_fderiv (by norm_num)
  have hγcont : Continuous (fun θ : ℝ => r * Complex.exp (θ * Complex.I)) := by fun_prop
  have hφcont : Continuous φ := by
    rw [hφ]
    exact (continuous_norm.comp (hfdc.comp hγcont)).const_mul r
  have hint : IntegrableOn φ (Set.Icc a b) := hφcont.continuousOn.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc a b)] φ :=
    ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => by
      rw [hφ]
      exact mul_nonneg hr (norm_nonneg _)
  -- bridge the interval Bochner integral and the `ℝ≥0∞`-valued set integral
  have hconv : ENNReal.ofReal (∫ θ in a..b, φ θ)
      = ∫⁻ θ in Set.Icc a b, ENNReal.ofReal (φ θ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  calc ENNReal.ofReal
        ‖g (r * Complex.exp (b * Complex.I)) - g (r * Complex.exp (a * Complex.I))‖
      ≤ ENNReal.ofReal (∫ θ in a..b, φ θ) := ENNReal.ofReal_le_ofReal hdisp
    _ = ∫⁻ θ in Set.Icc a b, ENNReal.ofReal (φ θ) := hconv

end Work.Fatou.Analysis

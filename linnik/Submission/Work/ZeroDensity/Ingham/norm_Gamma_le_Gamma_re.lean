import Mathlib

open MeasureTheory Set Real

namespace Work.ZeroDensity.Ingham

/-- **Pointwise bound for the complex `Γ` function.**  On the half-plane `0 < Re s` we have
`‖Γ s‖ ≤ Γ (Re s)`; equivalently, `s ↦ Γ s` is dominated by its real restriction along the
real axis.  Both sides are Euler integrals:
`Complex.Gamma_eq_integral` writes `Γ s = ∫_{0}^{∞} t^{s-1} e^{-t} dt` and
`Real.Gamma_eq_integral` writes `Γ (Re s) = ∫_{0}^{∞} t^{Re s - 1} e^{-t} dt`; taking norms
under the first integral and using `Complex.norm_cpow_eq_rpow_re_of_pos` gives the claim. -/
theorem norm_Gamma_le_Gamma_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  let f : ℝ → ℂ := fun x : ℝ => ↑(rexp (-x)) * ↑x ^ (s - 1)
  have hni := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ))) (f := f)
  have hre : (s - 1 : ℂ).re = s.re - 1 := by simp
  calc
    ‖Complex.Gamma s‖ = ‖Complex.GammaIntegral s‖ := by
      rw [Complex.Gamma_eq_integral hs]
    _ ≤ ∫ x : ℝ in Ioi 0, ‖f x‖ := by
      simpa [Complex.GammaIntegral, f] using hni
    _ = ∫ x : ℝ in Ioi 0, rexp (-x) * x ^ (s.re - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      have hxpos : 0 < x := by simpa using hx
      simp only [f]
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _),
        Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      rw [hre]
    _ = Real.Gamma s.re := by
      exact (Real.Gamma_eq_integral hs).symm

end Work.ZeroDensity.Ingham

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open Filter Set Real MeasureTheory Asymptotics
open scoped Nat Topology ComplexConjugate

set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- For `0 < Re s` the modulus of the complex Gamma function at `s` is at most its value
at the real point `Re s`: `‖Γ(s)‖ ≤ ‖Γ(Re s)‖`. -/
theorem norm_Gamma_le_norm_Gamma_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s.re : ℂ)‖ := by
  let f : ℝ → ℂ := fun x : ℝ => ↑(rexp (-x)) * ↑x ^ (s - 1)
  have hni := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ))) (f := f)
  have hre : (s - 1 : ℂ).re = s.re - 1 := by simp
  have hGamma_nonneg : 0 ≤ Real.Gamma s.re := (Real.Gamma_pos_of_pos hs).le
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
    _ = ‖(Real.Gamma s.re : ℂ)‖ := by
      exact (Complex.norm_of_nonneg hGamma_nonneg).symm
    _ = ‖Complex.Gamma (s.re : ℂ)‖ := by
      rw [Complex.Gamma_ofReal]

end Commons.Analysis.SpecialFunctions.Gamma
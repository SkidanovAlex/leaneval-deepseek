import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Euler's integral for the Euler--Mascheroni constant

We prove `∫ t in Ioi 0, log t * exp (-t) = -γ` (where `γ` is the Euler--Mascheroni
constant) by differentiating the Gamma integral representation of `Γ(s)` at `s = 1`.

The (complex) Gamma integral `Complex.GammaIntegral s = ∫ t in Ioi 0, exp (-t) * t ^ (s - 1)`
agrees with `Complex.Gamma` on the half-plane `0 < re s`.  Mathlib's Mellin-transform
machinery (`Complex.hasDerivAt_GammaIntegral`) computes its derivative as the Mellin
transform of `log t * exp (-t)`, i.e. `∫ t in Ioi 0, t ^ (s - 1) * (log t * exp (-t))`.
At `s = 1` this is exactly the integral in the statement, and by
`Complex.hasDerivAt_Gamma_one` (from `Mathlib.NumberTheory.Harmonic.GammaDeriv`) the
derivative of `Γ` at `1` equals `-γ`.
-/

namespace Commons.Analysis.SpecialFunctions

theorem eulerIntegral_log_exp_neg :
    (∫ t : ℝ in Set.Ioi 0, Real.log t * Real.exp (-t)) = -Real.eulerMascheroniConstant := by
  -- Derivative of the complex Gamma integral at `s = 1` is our integral, viewed in `ℂ`.
  have hGi_raw := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num : 0 < (1 : ℂ).re)
  have hGi : HasDerivAt Complex.GammaIntegral
      (∫ t : ℝ in Set.Ioi 0, ((Real.log t * Real.exp (-t) : ℝ) : ℂ)) (1 : ℂ) := by
    refine hGi_raw.congr_deriv ?_
    -- At `s = 1` the factor `t ^ (s - 1)` equals `1` pointwise on `t > 0`.
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    norm_num [Complex.cpow_zero, Complex.ofReal_mul]
  -- ... and `Γ` agrees with its integral representation on a neighbourhood of `1`, so
  -- the derivative of the Gamma integral at `1` is also the derivative of `Γ` at `1`.
  have hG' : HasDerivAt Complex.GammaIntegral (-(Real.eulerMascheroniConstant : ℂ)) (1 : ℂ) := by
    apply Complex.hasDerivAt_Gamma_one.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (0 : ℝ) < (1 : ℂ).re)] with s hs
    exact (Complex.Gamma_eq_integral hs).symm
  have hComplex :
      (∫ t : ℝ in Set.Ioi 0, ((Real.log t * Real.exp (-t) : ℝ) : ℂ)) =
        -(Real.eulerMascheroniConstant : ℂ) :=
    HasDerivAt.unique hGi hG'
  -- Passing a real integrand through `↑ : ℝ → ℂ` commutes with integration.
  have hJ : (∫ t : ℝ in Set.Ioi 0, ((Real.log t * Real.exp (-t) : ℝ) : ℂ)) =
      ↑(∫ t : ℝ in Set.Ioi 0, Real.log t * Real.exp (-t)) := by
    simpa using (integral_ofReal (𝕜 := ℂ) (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (f := fun t : ℝ => Real.log t * Real.exp (-t)))
  exact_mod_cast (hJ.symm.trans hComplex)

end Commons.Analysis.SpecialFunctions
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.Theta
import Submission.Work.BoseFixR.LatGreen.integral_rpow_neg_three_halves_mul_exp_neg_div
import Submission.Work.BoseFixR.LatGreen.rpow_neg_three_halves_mul_sqrt_pi_div_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Green's function of `−Δ` on `ℝ³` from the heat kernel

The fundamental solution of `−Δ` in `ℝ³` is `x ↦ 1/(4π‖x‖)`.  Since the heat kernel
`heatK3 t x = (4πt)^{-3/2} exp(−‖x‖²/(4t))` of `∂_t = Δ` is the kernel of `e^{tΔ}`, the
fundamental solution is the time-integral of the heat kernel:

  `∫_0^∞ heatK3 t x dt = 1/(4π‖x‖)`   for `x ≠ 0`,

which is this module's theorem `HeatIntegral`.  This is the analytic input identifying the
`−1/4π‖·‖` part of the `ℤ³`-lattice Green's function (see `LatGreen.Theta`).

**Proof.**  Writing `r = ‖x‖` and `a = r²/4 > 0`, the pointwise identity
`heatK3 t x = (4πt)^{-3/2} e^{-a/t}` on `t > 0` turns the integral into a pure
one-dimensional Laplace-type integral, decomposed as

* `(4πt)^{-3/2} = (4π)^{-3/2} t^{-3/2}` (rpow of a product), so the constant `(4π)^{-3/2}`
  factors out of the integral (`integral_const_mul`);
* the engine `∫_0^∞ t^{-3/2} e^{-a/t} dt = √(π/a)` — proved by the change of variables
  `t = a/u`, which turns it into the Euler integral `∫_0^∞ u^{-1/2} e^{-u} du = Γ(1/2) = √π`
  (`integral_rpow_neg_three_halves_mul_exp_neg_div`);
* the arithmetic normalisation `(4π)^{-3/2} √(π/a) = 1/(8π√a)`
  (`rpow_neg_three_halves_mul_sqrt_pi_div_eq`) and `√(r²/4) = r/2`, giving `1/(4πr)`.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

/-- The heat kernel integral of `−Δ` on `ℝ³`: for `x ≠ 0`,
`∫_0^∞ heatK3 t x dt = 1/(4π‖x‖)`. -/
theorem HeatIntegral {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    ∫ t in Set.Ioi (0 : ℝ), Work.BoseFixR.LatGreen.heatK3 t x
      = 1 / (4 * Real.pi * ‖x‖) := by
  set a : ℝ := ‖x‖ ^ 2 / 4 with ha_def
  have ha : 0 < a := by rw [ha_def]; positivity
  -- (1) pointwise rewriting of the heat kernel integrand
  have h1 : ∫ t in Set.Ioi (0 : ℝ), heatK3 t x
      = ∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (mem_Ioi.mp ht)
    simp only [heatK3]
    have hexp : -‖x‖ ^ 2 / (4 * t) = -(a / t) := by rw [ha_def]; field_simp
    rw [hexp]
  -- (2) factor the constant `(4π)^{-3/2}` out of the integral
  have h2 : ∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t))
      = (4 * Real.pi) ^ (-(3 / 2 : ℝ))
          * ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    beta_reduce
    rw [Real.mul_rpow (by positivity) (le_of_lt (mem_Ioi.mp ht))]
    ring
  -- (3) the one-dimensional engine, and the constant normalisation
  rw [h1, h2, integral_rpow_neg_three_halves_mul_exp_neg_div ha,
    rpow_neg_three_halves_mul_sqrt_pi_div_eq ha]
  -- (4) `√(‖x‖²/4) = ‖x‖/2` finishes
  rw [ha_def]
  have hsq : Real.sqrt (‖x‖ ^ 2 / 4) = ‖x‖ / 2 := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2), Real.sqrt_sq (norm_nonneg x)]
    norm_num
  rw [hsq]
  field_simp
  ring

end Work.BoseFixR.LatGreen

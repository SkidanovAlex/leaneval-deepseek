import Mathlib
import Submission.Work.Pert.PinLogDev.Helpers

/-!
# `Work.Pert.PinLogDev.axis_integral_le`

The axis transport of `PinLogDev` integrates the pointwise derivative bound
`‖Φ' - 1‖ ≤ √2 C₂ / min (margA) (margB) + (32/31) ‖F z - (z+1)‖` along the line `Re = 0`, once
with the *growing* radius `R(s) = (s - Ξ)/2` (giving the `1/(s - Ξ)` term) and once with a fixed
radius (which stays on the right-hand side of the inequality).

The lemma below is the purely elementary bookkeeping step: the *linear* combination of the three
one-dimensional integrals that appears on the left is bounded by the corresponding *linear*
combination of their values.  In fact both sides are **equal**: by `∫ ds/(s - Ξ) = log((b-Ξ)/(a-Ξ))`
and `∫ ds/s = log(b/a)` (`integral_one_div_sub`, `integral_one_div_self` in `Helpers`) the right
side is literally the left side, the only input being that the coefficients `√2 C₂` and
`(32/31) Kd` are pulled out of the integral (`integral_const_mul`) and that the integral of a sum
splits (`integral_add`).
-/

namespace Work.Pert.PinLogDev

open MeasureTheory

theorem axis_integral_le {Cα M Kd C₂ Ξ a b : ℝ}
    (hCα : 0 < Cα) (hKd : 0 ≤ Kd) (hC₂ : 0 ≤ C₂)
    (ha : 0 < a) (hΞa : Ξ < a) (hab : a ≤ b) :
    (∫ s in a..b, (Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ))
        + ((32 : ℝ) / 31) * Kd * (1 / s)))
      ≤ Real.sqrt 2 * C₂ * (Real.log ((b - Ξ) / (a - Ξ))
          + ∫ s in a..b, (1 : ℝ) / (Cα + |s - M|))
        + ((32 : ℝ) / 31) * Kd * Real.log (b / a) := by
  have hI1 : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / (Cα + |s - M|)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun s _ => by positivity)
  -- `s ↦ 1/(s - Ξ)` is continuous on `[a, b]` because `Ξ < a ≤ s`
  have hI2 : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / (s - Ξ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.div₀ continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun s hs => ne_of_gt (by have := hs.1; linarith))
  -- `s ↦ 1/s` is continuous on `[a, b]` because `a > 0`
  have hI3 : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / s) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.div₀ continuousOn_const continuousOn_id
      (fun s hs => ne_of_gt (by have := hs.1; linarith))
  have hI12 : IntervalIntegrable (fun s : ℝ => (1 : ℝ) / (Cα + |s - M|) + 1 / (s - Ξ))
      volume a b :=
    hI1.add hI2
  have hFa : IntervalIntegrable
      (fun s : ℝ => Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ))) volume a b :=
    hI12.const_mul _
  have hGb : IntervalIntegrable (fun s : ℝ => (32 : ℝ) / 31 * Kd * (1 / s)) volume a b :=
    hI3.const_mul _
  -- The two sides are equal: pull out the constants, split the sum, evaluate the two elementary
  -- integrals and rearrange.
  have hkey : (∫ s in a..b, (Real.sqrt 2 * C₂ * (1 / (Cα + |s - M|) + 1 / (s - Ξ))
        + ((32 : ℝ) / 31) * Kd * (1 / s)))
      = Real.sqrt 2 * C₂ * (Real.log ((b - Ξ) / (a - Ξ))
          + ∫ s in a..b, (1 : ℝ) / (Cα + |s - M|))
        + ((32 : ℝ) / 31) * Kd * Real.log (b / a) := by
    rw [intervalIntegral.integral_add hFa hGb]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add hI1 hI2]
    rw [integral_one_div_sub hΞa hab, integral_one_div_self ha hab]
    ring
  exact le_of_eq hkey

end Work.Pert.PinLogDev

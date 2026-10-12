import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseKinLoc.Momentum

/-- Cauchy–Schwarz / Jensen for the integral over `[0,1]` (which has measure one):
the square of the integral of `g` is at most the integral of `g ^ 2`.  The proof is the
standard "complete the square" argument: `0 ≤ ∫ (g t - m)^2 = ∫ g^2 - m^2` where
`m = ∫ g`. -/
theorem interval_integral_sq_le (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 1)
    (hg2 : IntervalIntegrable (fun t : ℝ => g t ^ 2) volume 0 1) :
    (∫ t in (0:ℝ)..1, g t) ^ 2 ≤ ∫ t in (0:ℝ)..1, g t ^ 2 := by
  set m : ℝ := ∫ t in (0:ℝ)..1, g t with hm
  -- the square of the mean deviation is nonnegative
  have hkey : 0 ≤ ∫ t in (0:ℝ)..1, (g t - m) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun u _ => sq_nonneg _
  have h1 : IntervalIntegrable (fun t : ℝ => g t ^ 2) volume 0 1 := hg2
  have h2 : IntervalIntegrable (fun t : ℝ => (2 * m) * g t) volume 0 1 := hg.const_mul _
  have h3 : IntervalIntegrable (fun _ : ℝ => m ^ 2) volume 0 1 := intervalIntegrable_const
  -- expand the square
  have hcongr : ∫ t in (0:ℝ)..1, (g t - m) ^ 2
      = ∫ t in (0:ℝ)..1, (g t ^ 2 - (2 * m) * g t + m ^ 2) :=
    intervalIntegral.integral_congr fun t _ => by ring
  -- and integrate termwise
  have hsplit : ∫ t in (0:ℝ)..1, (g t ^ 2 - (2 * m) * g t + m ^ 2)
      = (∫ t in (0:ℝ)..1, g t ^ 2) - m ^ 2 := by
    rw [intervalIntegral.integral_add (h1.sub h2) h3, intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    rw [hm]
    simp
    ring
  rw [hcongr, hsplit] at hkey
  linarith

end Work.BoseKinLoc.Momentum

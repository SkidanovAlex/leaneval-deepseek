import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Measure.Real

open MeasureTheory Metric Filter Set
open scoped Topology

/-- `∫_{r ∈ (a,b]} r/(1+r²) dr ≤ b/a - 1` for `0 < a ≤ b`. -/
theorem setIntegral_Ioc_mul_inv_one_add_sq_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in Set.Ioc a b, r / (1 + r ^ 2)) ≤ b / a - 1 := by
  rw [← intervalIntegral.integral_of_le hab]
  have hcont : Continuous fun r : ℝ => r / (1 + r ^ 2) := by
    refine Continuous.div continuous_id ?_ ?_
    · fun_prop
    · intro x
      positivity
  have hf : IntervalIntegrable (fun r : ℝ => r / (1 + r ^ 2)) volume a b :=
    hcont.intervalIntegrable a b
  have hg : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / a) volume a b :=
    intervalIntegrable_const
  have hmono : (∫ r in a..b, r / (1 + r ^ 2)) ≤ ∫ r in a..b, (1 : ℝ) / a :=
    intervalIntegral.integral_mono_on hab hf hg (fun x hx => by
      have hxge : a ≤ x := hx.1
      have hxpos : 0 < x := lt_of_lt_of_le ha hxge
      have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
      rw [div_le_iff₀ h1, div_mul_eq_mul_div, one_mul, le_div_iff₀ ha]
      nlinarith [hxge, ha, sq_nonneg x])
  rw [intervalIntegral.integral_const] at hmono
  have hconst : (b - a) • ((1 : ℝ) / a) = b / a - 1 := by
    rw [smul_eq_mul]
    field_simp
  linarith [hmono, le_of_eq hconst]

end Commons.Measure.Real
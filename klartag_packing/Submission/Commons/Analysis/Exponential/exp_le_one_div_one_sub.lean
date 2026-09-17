import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Complex.Exponential

namespace Commons.Analysis.Exponential

theorem exp_le_one_div_one_sub {t : ℝ} (ht : t < 1) : Real.exp t ≤ 1 / (1 - t) := by
  have hu : 0 < 1 - t := by linarith
  -- Key bound: exp(1 - t) ≥ exp 1 * (1 - t), from exp(x) ≥ x + 1 at x = -t.
  have h1 : Real.exp 1 * (1 - t) ≤ Real.exp (1 - t) := by
    have h := Real.add_one_le_exp (1 - t - 1)
    rw [show (1 - t - 1) + 1 = 1 - t from by ring] at h
    rw [Real.exp_sub] at h
    rw [le_div_iff₀ (Real.exp_pos 1)] at h
    linarith [h, mul_comm (1 - t) (Real.exp 1)]
  have hpos : 0 < Real.exp 1 * (1 - t) := mul_pos (Real.exp_pos 1) hu
  -- Rewrite exp t using exp 1 = exp t * exp(1 - t).
  have h3 : Real.exp t = Real.exp 1 / Real.exp (1 - t) := by
    have hone : Real.exp 1 = Real.exp t * Real.exp (1 - t) := by
      rw [← Real.exp_add]; ring_nf
    rw [hone, mul_div_cancel_right₀ (Real.exp t) (ne_of_gt (Real.exp_pos (1 - t)))]
  rw [h3]
  calc Real.exp 1 / Real.exp (1 - t)
      ≤ Real.exp 1 / (Real.exp 1 * (1 - t)) :=
        div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos 1)) hpos h1
    _ = 1 / (1 - t) := by
        rw [div_mul_eq_div_div]
        rw [div_self (ne_of_gt (Real.exp_pos 1))]

end Commons.Analysis.Exponential
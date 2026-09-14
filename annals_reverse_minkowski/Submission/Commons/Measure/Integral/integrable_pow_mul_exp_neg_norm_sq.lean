import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm

namespace Commons.Measure.Integral

open MeasureTheory
open scoped Real

/-- For every `m : ℕ` and `c > 0` the function `t ↦ t ^ m * exp (-c * t ^ 2)` is bounded on
`[0, ∞)` by an explicit constant.  The proof takes logarithms: `log t ≤ t - 1` gives
`m * log t ≤ m * t - m`, and `m * t - c * t ^ 2 ≤ m ^ 2 / (4 c)` is a sum-of-squares identity. -/
private lemma pow_mul_exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ m * Real.exp (-c * t ^ 2) ≤ Real.exp ((m : ℝ) ^ 2 / (4 * c) - m) := by
  rcases eq_or_lt_of_le ht with h | htpos
  · subst h
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · rw [zero_pow hm.ne', zero_mul]
      exact (Real.exp_pos _).le
  · have hlog : Real.log (t ^ m * Real.exp (-c * t ^ 2)) ≤ (m : ℝ) ^ 2 / (4 * c) - m := by
      rw [Real.log_mul (pow_ne_zero _ htpos.ne') (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
      have h1 : (m : ℝ) * Real.log t ≤ (m : ℝ) * (t - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos htpos) (Nat.cast_nonneg m)
      have hmain : (m : ℝ) * t - c * t ^ 2 ≤ (m : ℝ) ^ 2 / (4 * c) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * c)]
        nlinarith [sq_nonneg ((m : ℝ) - 2 * c * t)]
      linarith [h1, hmain]
    calc t ^ m * Real.exp (-c * t ^ 2)
        = Real.exp (Real.log (t ^ m * Real.exp (-c * t ^ 2))) :=
          (Real.exp_log (mul_pos (pow_pos htpos m) (Real.exp_pos _))).symm
      _ ≤ Real.exp ((m : ℝ) ^ 2 / (4 * c) - m) := Real.exp_le_exp.mpr hlog

/-- Polynomial growth is dominated by Gaussian decay: for `t ≥ 0`,
`(1 + t) ^ N * exp (-c * t ^ 2)` is bounded by an explicit constant.  It combines the elementary
bound `(1 + t) ^ N ≤ 2 ^ (N - 1) * (1 + t ^ N)` (`add_pow_le`) with
`pow_mul_exp_neg_mul_sq_le` and `exp (-c * t ^ 2) ≤ 1`. -/
private lemma one_add_pow_mul_exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) (N : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    (1 + t) ^ N * Real.exp (-c * t ^ 2) ≤
      (2 : ℝ) ^ (N - 1) * (1 + Real.exp ((N : ℝ) ^ 2 / (4 * c) - N)) := by
  have hK := pow_mul_exp_neg_mul_sq_le (c := c) hc N ht
  have hexp1 : Real.exp (-c * t ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg t, hc]
  have h2 : (1 + t) ^ N ≤ (2 : ℝ) ^ (N - 1) * (1 + t ^ N) := by
    simpa using add_pow_le (a := (1 : ℝ)) (b := t) zero_le_one ht N
  calc (1 + t) ^ N * Real.exp (-c * t ^ 2)
      ≤ ((2 : ℝ) ^ (N - 1) * (1 + t ^ N)) * Real.exp (-c * t ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (2 : ℝ) ^ (N - 1) *
          (Real.exp (-c * t ^ 2) + t ^ N * Real.exp (-c * t ^ 2)) := by ring
    _ ≤ (2 : ℝ) ^ (N - 1) * (1 + Real.exp ((N : ℝ) ^ 2 / (4 * c) - N)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
        linarith

theorem integrable_pow_mul_exp_neg_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (b : ℝ) (hb : 0 < b) (N : ℕ) : MeasureTheory.Integrable (fun x : E => (1 + ‖x‖) ^ N * Real.exp (-b * ‖x‖ ^ 2)) MeasureTheory.volume := by
  have hc : 0 < b / 2 := by linarith
  set C : ℝ := (2 : ℝ) ^ (N - 1) * (1 + Real.exp ((N : ℝ) ^ 2 / (4 * (b / 2)) - N)) with hC
  refine (Integrable.const_mul (integrable_rexp_neg_mul_sq_norm (b / 2) hc) C).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with x
    have hx := one_add_pow_mul_exp_neg_mul_sq_le (c := b / 2) hc N (norm_nonneg x)
    have heq : Real.exp (-(b / 2) * ‖x‖ ^ 2) * Real.exp (-(b / 2) * ‖x‖ ^ 2) =
        Real.exp (-b * ‖x‖ ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) N) (Real.exp_pos _).le)]
    calc (1 + ‖x‖) ^ N * Real.exp (-b * ‖x‖ ^ 2)
        = (1 + ‖x‖) ^ N *
            (Real.exp (-(b / 2) * ‖x‖ ^ 2) * Real.exp (-(b / 2) * ‖x‖ ^ 2)) := by rw [heq]
      _ = ((1 + ‖x‖) ^ N * Real.exp (-(b / 2) * ‖x‖ ^ 2)) *
            Real.exp (-(b / 2) * ‖x‖ ^ 2) := by ring
      _ ≤ C * Real.exp (-(b / 2) * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le

end Commons.Measure.Integral
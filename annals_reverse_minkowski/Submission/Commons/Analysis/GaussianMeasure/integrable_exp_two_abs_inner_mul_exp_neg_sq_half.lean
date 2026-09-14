import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm

namespace Commons.Analysis.GaussianMeasure

theorem integrable_exp_two_abs_inner_mul_exp_neg_sq_half {n : ℕ} (t : EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (2 * |inner ℝ t x|) * Real.exp (-‖x‖ ^ 2 / 2))
      MeasureTheory.volume := by
  have hg : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        Real.exp (4 * ‖t‖ ^ 2) * Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2)) MeasureTheory.volume :=
    (Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin n))
      (1 / 4) (by norm_num)).const_mul _
  refine MeasureTheory.Integrable.mono hg ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (mul_pos (Real.exp_pos _) (Real.exp_pos _))),
      abs_of_nonneg (le_of_lt (mul_pos (Real.exp_pos _) (Real.exp_pos _)))]
    have key : 2 * |inner ℝ t x| - ‖x‖ ^ 2 / 2 ≤ 4 * ‖t‖ ^ 2 - ‖x‖ ^ 2 / 4 := by
      have h1 : |inner ℝ t x| ≤ ‖t‖ * ‖x‖ := abs_real_inner_le_norm t x
      nlinarith [sq_nonneg (2 * ‖t‖ - ‖x‖ / 2)]
    calc Real.exp (2 * |inner ℝ t x|) * Real.exp (-‖x‖ ^ 2 / 2)
        = Real.exp (2 * |inner ℝ t x| - ‖x‖ ^ 2 / 2) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (4 * ‖t‖ ^ 2 - ‖x‖ ^ 2 / 4) := Real.exp_le_exp.mpr key
      _ = Real.exp (4 * ‖t‖ ^ 2) * Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring

end Commons.Analysis.GaussianMeasure
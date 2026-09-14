import Mathlib
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm

namespace Commons.Analysis.GaussianMeasure

theorem integrable_exp_neg_norm_sq_half {n : ℕ} :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / 2))
      MeasureTheory.volume := by
  have h := Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin n)) (1 / 2) (by norm_num)
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / 2))
      = fun x => Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) := by
    funext x
    congr 1
    ring
  rw [heq]
  exact h

end Commons.Analysis.GaussianMeasure

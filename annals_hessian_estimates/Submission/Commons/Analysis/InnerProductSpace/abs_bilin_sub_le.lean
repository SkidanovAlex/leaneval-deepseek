import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

namespace Commons.Analysis.InnerProductSpace

/-- A symmetric-type estimate for a continuous bilinear form: for a continuous linear map
`Q : E →L[ℝ] E →L[ℝ] ℝ` regarded as a bilinear form `(x, y) ↦ Q x y`, the difference
`Q a a - Q b b` is bounded by `‖Q‖ * (‖a‖ + ‖b‖) * ‖a - b‖`.

The proof splits `Q a a - Q b b = Q a (a - b) + Q (a - b) b` (linearity in each slot) and
applies the operator-norm bound `‖Q x y‖ ≤ ‖Q‖ ‖x‖ ‖y‖` to each term. -/
theorem abs_bilin_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) :
    |Q a a - Q b b| ≤ ‖Q‖ * (‖a‖ + ‖b‖) * ‖a - b‖ := by
  have h1 : Q a a - Q b b = Q a (a - b) + Q (a - b) b := by
    rw [map_sub (Q a) a b, map_sub Q a b, sub_apply]
    ring
  calc |Q a a - Q b b|
      = |Q a (a - b) + Q (a - b) b| := by rw [h1]
    _ ≤ |Q a (a - b)| + |Q (a - b) b| := abs_add_le _ _
    _ ≤ ‖Q‖ * ‖a‖ * ‖a - b‖ + ‖Q‖ * ‖a - b‖ * ‖b‖ := by
          apply add_le_add
          · calc |Q a (a - b)| = ‖Q a (a - b)‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖Q a‖ * ‖a - b‖ := ContinuousLinearMap.le_opNorm (Q a) (a - b)
              _ ≤ (‖Q‖ * ‖a‖) * ‖a - b‖ := by
                    apply mul_le_mul_of_nonneg_right
                    · exact ContinuousLinearMap.le_opNorm Q a
                    · exact norm_nonneg _
          · calc |Q (a - b) b| = ‖Q (a - b) b‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖Q (a - b)‖ * ‖b‖ := ContinuousLinearMap.le_opNorm (Q (a - b)) b
              _ ≤ (‖Q‖ * ‖a - b‖) * ‖b‖ := by
                    apply mul_le_mul_of_nonneg_right
                    · exact ContinuousLinearMap.le_opNorm Q (a - b)
                    · exact norm_nonneg _
    _ = ‖Q‖ * (‖a‖ + ‖b‖) * ‖a - b‖ := by ring

end Commons.Analysis.InnerProductSpace
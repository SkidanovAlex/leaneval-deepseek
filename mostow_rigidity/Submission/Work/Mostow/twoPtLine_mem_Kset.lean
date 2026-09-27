import Mathlib
import Submission.Work.Mostow.PhiMaxLine
import Submission.Work.Mostow.LinAlgMatrixIneqAux

namespace Work.Mostow

/-- The two-point perturbation of a point of the box `Kset n δ` stays in the box, as long as the
mass `t` moved from coordinate `j` to coordinate `i` is smaller than the distance `ε` of both
`x i` and `x j` from the lower bound `δ`.  The sum of the coordinates is preserved, and each
coordinate is moved strictly above `δ`. -/
theorem twoPtLine_mem_Kset {n : ℕ} {δ : ℝ} {x : Fin n → ℝ} (hx : x ∈ Kset n δ)
    {i j : Fin n} (hij : i ≠ j) {ε t : ℝ} (hεi : ε ≤ x i - δ) (hεj : ε ≤ x j - δ)
    (ht : |t| < ε) : TwoPtLine x i j t ∈ Kset n δ := by
  refine ⟨?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · rw [hki, TwoPtLine_apply_left x hij t]
      have h2 : -(|t|) ≤ t := neg_abs_le t
      linarith
    · by_cases hkj : k = j
      · rw [hkj, TwoPtLine_apply_right x hij t]
        have h2 : t ≤ |t| := le_abs_self t
        linarith
      · rw [TwoPtLine_apply_of_ne x hki hkj t]
        exact hx.1 k
  · rw [twoPtLine_sum, hx.2]

end Work.Mostow

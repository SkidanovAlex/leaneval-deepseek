import Mathlib
import Submission.Work.EKLC7.TentDef

/-!
# `tentFormula` is dominated by the indicator of `Icc a (b+1)`

The tent function `tentFormula a b n` takes values in `[0,1]`, and vanishes
outside the interval `[a, b + 1]` (the support of the trapezoid of base
`[a, b + 1]`).  Hence it is pointwise bounded above by the indicator function
of `Set.Icc a (b+1)`.

No hypothesis `a < b` is needed: the support of the trapezoid is always
contained in `[a, b+1]` (for `a > b + 1` the latter interval is empty while the
tent still vanishes there).
-/

namespace Work.EKLC7

theorem tent_formula_le_indicator (a b : ℚ) (n : ℕ) (t : ℝ) :
    tentFormula a b n t ≤ (Set.Icc (a : ℝ) ((b : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) t := by
  by_cases h : t ∈ Set.Icc (a : ℝ) ((b : ℝ) + 1)
  · rw [Set.indicator_of_mem h]
    unfold tentFormula
    exact max_le zero_le_one (min_le_left 1 _)
  · rw [Set.indicator_of_notMem h]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
    unfold tentFormula
    rcases h with ht | ht
    · -- `t < a`: the first slope factor is `≤ 0`
      refine max_le le_rfl ?_
      refine le_trans (min_le_right 1 _) ?_
      refine le_trans (min_le_left _ _) ?_
      refine mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) ?_
      linarith
    · -- `b + 1 < t`: either `n = 0`, or the second slope factor is `≤ 0`
      refine max_le le_rfl ?_
      refine le_trans (min_le_right 1 _) ?_
      rcases n with _ | n
      · simp
      · refine le_trans (min_le_right _ _) ?_
        push_cast
        have hbt : (b : ℝ) - t < -1 := by linarith
        have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
        have hprod : ((n : ℝ) + 1) * ((b : ℝ) - t) ≤ ((n : ℝ) + 1) * (-1) :=
          mul_le_mul_of_nonneg_left (le_of_lt hbt) hnn
        nlinarith [hprod, Nat.cast_nonneg (α := ℝ) n]

end Work.EKLC7

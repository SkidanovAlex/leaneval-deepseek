import Mathlib
import Submission.Work.TMComp.C7Aux.rtlSchedule

namespace Work.TMC7Core.Scale

open Work.TMComp.C7Aux

/-- `rtlMM` is the multiplier `Q i * max 1 ⌊exp(cκ Q i / 2)/(5 Q i)⌋`. When the exponential
dominates `6 Q i`, the multiplier's double is still below the exponential: the floor is at
least one, so the multiplier is at most `Q i * exp(cκ Q i/2)/(5 Q i) = exp(cκ Q i/2)/5`. -/
theorem rtlMMTwoMulLtV2 (cκ : ℝ) (Q : ℕ → ℕ) (i : ℕ)
    (h : 6 * (Q i : ℝ) ≤ Real.exp (cκ * (Q i : ℝ) / 2)) :
    2 * (Work.TMComp.C7Aux.rtlMM cκ Q i : ℝ) < Real.exp (cκ * (Q i : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos (Q i) with hq | hq
  · -- degenerate case: `Q i = 0` makes the multiplier vanish, and the exponential is positive
    have hz : rtlMM cκ Q i = 0 := by
      unfold rtlMM
      rw [hq]
      norm_num
    rw [hz]
    norm_num
    exact Real.exp_pos _
  · have hq0 : (0 : ℝ) < (Q i : ℝ) := by exact_mod_cast hq
    have hE5q : 1 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)) := by
      rw [one_le_div (by positivity)]
      nlinarith [h]
    have hle := rtlMM_le cκ Q i hE5q
    nlinarith [hle, Real.exp_pos (cκ * (Q i : ℝ) / 2)]

end Work.TMC7Core.Scale

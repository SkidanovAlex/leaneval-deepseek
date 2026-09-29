import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Shift.Defs

namespace Work.IntLib.Shift

theorem shrCostBound : ∀ (p : ℕ) (R : List Bool) (m : ℕ), Work.IntLib.Shift.shrCost p R m ≤ m + R.length + 2 := by
  intro p R
  induction R generalizing p with
  | nil => intro m; simp
  | cons b bs ih =>
      intro m
      rw [shrCost_cons]
      by_cases h : m ≤ p
      · simp [h]
      · simp only [h, ite_false, List.length_cons]
        have hm : p ≤ m := le_of_lt (not_le.mp h)
        have h1 := ih (2 * p + b.toNat) (m - p)
        omega

end Work.IntLib.Shift

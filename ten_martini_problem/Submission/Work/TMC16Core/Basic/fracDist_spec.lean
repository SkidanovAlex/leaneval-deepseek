import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-- Basic specification of the distance-to-nearest-integer function
`fracDist x = |x - round x|`: it is nonnegative, at most `1/2`, invariant under
translation by integers, and vanishes exactly at the integers. -/
theorem fracDist_spec (x : ℝ) :
    (0 ≤ Work.TMC16Core.fracDist x) ∧ (Work.TMC16Core.fracDist x ≤ 1 / 2) ∧
      (∀ z : ℤ, Work.TMC16Core.fracDist (x + (z : ℝ)) = Work.TMC16Core.fracDist x) ∧
      (Work.TMC16Core.fracDist x = 0 ↔ ∃ z : ℤ, x = (z : ℝ)) := by
  refine ⟨abs_nonneg _, abs_sub_round x, ?_, ?_⟩
  · intro z
    rw [fracDist, fracDist, round_add_intCast]
    push_cast
    ring_nf
  · rw [fracDist, abs_eq_zero, sub_eq_zero]
    constructor
    · intro h; exact ⟨round x, h⟩
    · rintro ⟨z, rfl⟩; simp [round_intCast]

end Work.TMC16Core.Basic

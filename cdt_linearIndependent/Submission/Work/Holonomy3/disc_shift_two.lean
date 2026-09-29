import Mathlib
import Submission.Work.Holonomy3.lowdiscCells
import Submission.Work.Holonomy3.disc_shift_lipschitz

namespace Work.Holonomy3

open Submission.CDT.Discrepancy

/-- **The shift estimate with constant `2`.**  Moving every point of a configuration `t` of `d`
points of `[0,1)` by at most `η` (with `0 ≤ η`) changes the box discrepancy
(`Submission.CDT.Discrepancy.disc`) by at most `2·η`.

This is the sharp form of `disc_shift_lipschitz`, without the extra `1/d`: it follows by applying
the one-sided bound `disc_le_disc_add` (proved there) in the two directions. -/
theorem disc_shift_two {d : ℕ} (t u : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Ico 0 1) (hu : ∀ j, u j ∈ Set.Ico 0 1)
    {η : ℝ} (hη : 0 ≤ η) (h : ∀ j, |u j - t j| ≤ η) :
    |Submission.CDT.Discrepancy.disc u - Submission.CDT.Discrepancy.disc t| ≤ 2 * η := by
  have ht' : ∀ j, t j ∈ Set.Icc 0 1 := fun j => ⟨(ht j).1, le_of_lt (ht j).2⟩
  have hu' : ∀ j, u j ∈ Set.Icc 0 1 := fun j => ⟨(hu j).1, le_of_lt (hu j).2⟩
  have h1 : disc u ≤ disc t + 2 * η := disc_le_disc_add t u ht' hu' hη h
  have h2 : disc t ≤ disc u + 2 * η :=
    disc_le_disc_add u t hu' ht' hη fun j => by rw [abs_sub_comm]; exact h j
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

end Work.Holonomy3

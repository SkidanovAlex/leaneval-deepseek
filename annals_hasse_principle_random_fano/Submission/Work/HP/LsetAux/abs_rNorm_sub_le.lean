import Mathlib
import Submission.Work.HP.LsetAux.GridDefs

namespace Work.HP.LsetAux

/-- Reverse triangle inequality for the Euclidean norm `rNorm` on `ι → ℝ`:
`|‖v‖ - ‖w‖| ≤ ‖v - w‖`.

Note that `rNorm` is *not* Lean's norm on the function type `ι → ℝ` (that is the sup norm), so
this cannot be obtained from a generic `abs_norm_sub_norm_le` instance; we use the two
one-sided estimates `rNorm y ≤ rNorm a + rNorm (y - a)`. -/
theorem abs_rNorm_sub_le {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    |Work.HP.rNorm v - Work.HP.rNorm w| ≤ Work.HP.rNorm (v - w) := by
  have h₁ : Work.HP.rNorm v - Work.HP.rNorm w ≤ Work.HP.rNorm (v - w) := by
    have h := Work.HP.rNorm_le_add_sub v w
    linarith
  have h₂ : Work.HP.rNorm w - Work.HP.rNorm v ≤ Work.HP.rNorm (v - w) := by
    have h := Work.HP.rNorm_le_add_sub w v
    rw [Work.HP.rNorm_sub_comm w v] at h
    linarith
  exact abs_sub_le_iff.mpr ⟨h₁, h₂⟩

end Work.HP.LsetAux

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

/-- For `0 < α ≤ 1/4` we have `1/2 < cos α ^ 2`.

This is the quantitative smallness of `α` needed to make `cos` close to `1`:
since `2α ≤ 1/2 < π/2`, `cos (2α) > 0`, and `cos (2α) = 2 cos α ^ 2 - 1` then
gives `cos α ^ 2 > 1/2`. -/
lemma cos_sq_gt_half {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) : 1 / 2 < Real.cos α ^ 2 := by
  have h2pos : 0 < 2 * α := by linarith
  have h2lt : 2 * α < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hcos : 0 < Real.cos (2 * α) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2lt⟩
  have h := Real.cos_two_mul α
  nlinarith [h]

end Work.Diff.C

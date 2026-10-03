import Mathlib

namespace Work.Pert.Pin3

/-- For `‖w‖ ≤ 2/5`, the quantity `‖1 - exp w‖` is at least `‖w‖/2`: writing
`1 - exp w = -w - (exp w - 1 - w)` and using the quadratic remainder bound
`‖exp w - 1 - w‖ ≤ ‖w‖²` gives `‖1 - exp w‖ ≥ ‖w‖ - ‖w‖² ≥ ‖w‖/2`. -/
theorem exp_near_lower {w : ℂ} (hw : ‖w‖ ≤ 2 / 5) :
    ‖w‖ / 2 ≤ ‖(1 : ℂ) - Complex.exp w‖ := by
  have h1 : ‖w‖ ≤ 1 := by linarith
  have hb : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le h1
  have key : ‖w‖ - ‖Complex.exp w - 1 - w‖ ≤ ‖(1 : ℂ) - Complex.exp w‖ := by
    have heq : (1 : ℂ) - Complex.exp w = -w - (Complex.exp w - 1 - w) := by ring
    rw [heq]
    simpa using norm_sub_norm_le (-w) (Complex.exp w - 1 - w)
  have hsq : ‖w‖ ^ 2 ≤ ‖w‖ / 2 := by nlinarith [hw, norm_nonneg w]
  linarith

end Work.Pert.Pin3

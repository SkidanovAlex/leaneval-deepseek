import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `t ↦ log t` lies below its tangent: for `0 < u ≤ v`,
`u * log v - (v - u) ≤ u * log u`, i.e. `u * log (v/u) ≤ v - u`. -/
lemma log_concavity_floor (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    u * Real.log v - (v - u) ≤ u * Real.log u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hx : 0 < v / u := div_pos hv hu
  have h1 : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos hx
  have h2 : u * Real.log (v / u) ≤ u * (v / u - 1) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hu)
  rw [Real.log_div (ne_of_gt hv) (ne_of_gt hu)] at h2
  have h3 : u * (v / u - 1) = v - u := by
    field_simp
  linarith [h2, h3]

end Work.BW

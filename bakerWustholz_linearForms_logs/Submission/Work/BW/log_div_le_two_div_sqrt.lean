import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `log x ≤ 2 * √x` for `x ≥ 1`, from `log (√x) ≤ √x` and `log x = 2 * log (√x)`. -/
lemma log_le_two_mul_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (le_of_lt hxpos)]
    ring
  have hself : Real.log (Real.sqrt x) ≤ Real.sqrt x :=
    Real.log_le_self (le_of_lt hspos)
  linarith

/-- `log x / x ≤ 2/√x` for `x ≥ 1`, immediate from `log x ≤ 2√x`. -/
theorem log_div_le_two_div_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x / x ≤ 2 / Real.sqrt x := by
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  rw [div_le_div_iff₀ hxpos hspos]
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (le_of_lt hxpos)]
    ring
  have hself : Real.log (Real.sqrt x) ≤ Real.sqrt x :=
    Real.log_le_self (le_of_lt hspos)
  have hsq : Real.sqrt x * Real.sqrt x = x := by
    rw [← sq]; exact Real.sq_sqrt (le_of_lt hxpos)
  have h1 : 2 * Real.log (Real.sqrt x) ≤ 2 * Real.sqrt x := by linarith
  have h2 : (2 * Real.log (Real.sqrt x)) * Real.sqrt x ≤ (2 * Real.sqrt x) * Real.sqrt x :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt hspos)
  rw [hlog]
  calc (2 * Real.log (Real.sqrt x)) * Real.sqrt x ≤ (2 * Real.sqrt x) * Real.sqrt x := h2
    _ = 2 * (Real.sqrt x * Real.sqrt x) := by ring
    _ = 2 * x := by rw [hsq]

end Work.BW

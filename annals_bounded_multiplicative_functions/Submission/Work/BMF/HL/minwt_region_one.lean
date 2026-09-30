import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

/-- On the region `p ≤ y²` the weight `min 1 (2 / (min 1 (1/log y) · log p))` equals `1`:
both `min 1 (1/log y)` and `log p` are positive, and their product is at most `2` because
`min 1 (1/log y) ≤ 1/log y` and `log p ≤ log (y²) = 2 log y`. -/
theorem minwt_region_one {y : ℝ} (hy : 2 ≤ y) {p : ℕ} (hp : Nat.Prime p)
    (hpy : (p : ℝ) ≤ y ^ 2) :
    min 1 (2 / (min 1 (1 / Real.log y) * Real.log p)) = 1 := by
  have hy1 : (1 : ℝ) < y := by linarith
  have hlogy_pos : 0 < Real.log y := Real.log_pos hy1
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlogp_pos : 0 < Real.log p := Real.log_pos hp1
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp_le : Real.log p ≤ 2 * Real.log y := by
    have h : Real.log p ≤ Real.log (y ^ 2) := Real.log_le_log hp_pos hpy
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  set m := min 1 (1 / Real.log y) with hm
  have hm_pos : 0 < m := lt_min one_pos (div_pos one_pos hlogy_pos)
  have hm_le : m ≤ 1 / Real.log y := min_le_right _ _
  have hmul_le : m * Real.log p ≤ 2 := by
    calc m * Real.log p ≤ (1 / Real.log y) * Real.log p :=
          mul_le_mul_of_nonneg_right hm_le (le_of_lt hlogp_pos)
      _ = Real.log p / Real.log y := by ring
      _ ≤ 2 := by
          rw [div_le_iff₀ hlogy_pos]
          linarith
  have hmul_pos : 0 < m * Real.log p := mul_pos hm_pos hlogp_pos
  have hge : 1 ≤ 2 / (m * Real.log p) := by
    rw [one_le_div hmul_pos]
    exact hmul_le
  exact min_eq_left hge

end Work.BMF.HL

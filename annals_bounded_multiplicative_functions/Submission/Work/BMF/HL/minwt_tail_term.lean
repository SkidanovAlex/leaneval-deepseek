import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

theorem minwt_tail_term {y : ℝ} (hy : 2 ≤ y) {p : ℕ} (hp : Nat.Prime p) :
    min 1 (2 / (min 1 (1 / Real.log y) * Real.log p)) / (p : ℝ)
      ≤ (2 / min 1 (1 / Real.log y)) * (1 / ((p : ℝ) * Real.log p)) := by
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have ha : 0 < min 1 (1 / Real.log y) := lt_min one_pos (one_div_pos.mpr hlogy)
  calc min 1 (2 / (min 1 (1 / Real.log y) * Real.log p)) / (p : ℝ)
      ≤ (2 / (min 1 (1 / Real.log y) * Real.log p)) / (p : ℝ) :=
        div_le_div_of_nonneg_right (min_le_right _ _) (le_of_lt hpR)
    _ = (2 / min 1 (1 / Real.log y)) * (1 / ((p : ℝ) * Real.log p)) := by
        field_simp

end Work.BMF.HL

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

theorem loglog_floor_le (Q : ℝ) (hQ : 2 ≤ Q) :
    Real.log (Real.log Q) ≤ Real.log (Real.log (⌊Q⌋₊ : ℝ)) + Real.log 2 := by
  have hF2 : 2 ≤ ⌊Q⌋₊ := Nat.le_floor hQ
  have hFge : (2 : ℝ) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast hF2
  have hQpos : (0 : ℝ) < Q := by linarith
  have hFpos : (0 : ℝ) < (⌊Q⌋₊ : ℝ) := by linarith
  have hlt : Q < (⌊Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Q
  have hsq : Q ≤ (⌊Q⌋₊ : ℝ) * (⌊Q⌋₊ : ℝ) := by nlinarith [hFge, hlt]
  have hlogQ_le : Real.log Q ≤ 2 * Real.log (⌊Q⌋₊ : ℝ) := by
    have h := Real.log_le_log hQpos hsq
    rw [Real.log_mul (ne_of_gt hFpos) (ne_of_gt hFpos)] at h
    linarith
  have hlogQpos : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlogFpos : 0 < Real.log (⌊Q⌋₊ : ℝ) := Real.log_pos (by linarith)
  have h2 : Real.log (Real.log Q) ≤ Real.log (2 * Real.log (⌊Q⌋₊ : ℝ)) :=
    Real.log_le_log hlogQpos hlogQ_le
  rw [Real.log_mul (by norm_num) (ne_of_gt hlogFpos)] at h2
  linarith

end Work.BMF.SD

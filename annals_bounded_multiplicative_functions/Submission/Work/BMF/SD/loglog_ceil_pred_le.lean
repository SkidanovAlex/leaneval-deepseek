import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

theorem loglog_ceil_pred_le (P : ℝ) (hP : 2 ≤ P) (h : 2 ≤ ⌈P⌉₊ - 1) :
    Real.log (Real.log ((⌈P⌉₊ - 1 : ℕ) : ℝ)) ≤ Real.log (Real.log P) := by
  have hPpos : 0 < P := by linarith
  have hceil1 : 1 ≤ ⌈P⌉₊ := Nat.one_le_ceil_iff.mpr hPpos
  have hcast : ((⌈P⌉₊ - 1 : ℕ) : ℝ) = (⌈P⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil1]; norm_num
  have hle : ((⌈P⌉₊ - 1 : ℕ) : ℝ) ≤ P := by
    rw [hcast]
    have := Nat.ceil_lt_add_one (le_of_lt hPpos)
    linarith
  have h2 : (2 : ℝ) ≤ ((⌈P⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast h
  have hpos : 0 < ((⌈P⌉₊ - 1 : ℕ) : ℝ) := by linarith
  have hlog1 : Real.log ((⌈P⌉₊ - 1 : ℕ) : ℝ) ≤ Real.log P :=
    Real.log_le_log hpos hle
  have hlogpos : 0 < Real.log ((⌈P⌉₊ - 1 : ℕ) : ℝ) := by
    have := Real.log_le_log (by norm_num : (0:ℝ) < 2) h2
    have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  exact Real.log_le_log hlogpos hlog1

end Work.BMF.SD

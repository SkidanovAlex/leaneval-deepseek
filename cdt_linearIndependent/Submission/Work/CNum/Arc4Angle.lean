import Mathlib
import Submission.Work.CNum.AlpBound

namespace Work.CNum

/-- The numeric bound `244 * π / 512 < 1.4973`, the largest value the arc parameter
`(1024 - k) * π / 512` can take for `k ≥ 780`. -/
private lemma pi244_lt : (244 : ℝ) * Real.pi / 512 < 1.4973 := by
  nlinarith [Real.pi_lt_d4]

theorem Arc4Angle {k : ℕ} (h1 : 780 ≤ k) (h2 : k ≤ 1024) : (k : ℝ) * Real.pi / 512 - 2 * Real.pi ∈ Set.Ioo (-Work.CNum.alpR) Work.CNum.alpR := by
  have hAlp : (1.4973 : ℝ) < alpR := AlpBound.1
  have hk1 : (780 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
  have hk2 : (k : ℝ) ≤ 1024 := by exact_mod_cast h2
  set x : ℝ := ((1024 : ℝ) - k) * Real.pi / 512 with hx
  have hxnn : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (mul_nonneg (by linarith) Real.pi_pos.le) (by norm_num)
  have hx244 : x ≤ 244 * Real.pi / 512 := by
    rw [hx]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    nlinarith [Real.pi_pos]
  have hxlt : x < alpR := lt_of_le_of_lt hx244 (lt_trans pi244_lt hAlp)
  have hkey : (k : ℝ) * Real.pi / 512 - 2 * Real.pi = -x := by
    rw [hx]; ring
  rw [hkey]
  exact ⟨by linarith, by linarith⟩

end Work.CNum

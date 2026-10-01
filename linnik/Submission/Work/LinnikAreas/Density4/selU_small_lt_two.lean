import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs

namespace Work.LinnikAreas.Density4

/-- For `1 ≤ Q < 2` we have `⌊Q⌋₊ = 1`, hence `selU Q = μ(1)·log(Q/1)/1 = log Q`.
Since `0 ≤ log Q < log 2 < 1` we get `|log Q - 1| ≤ 1`, while
`(log 4)^3·(log (2+Q))^{-3} = (log 4 / log (2+Q))^3 ≥ 1` because
`log (2+Q) ≤ log 4` (as `Q < 2`). -/
theorem selU_small_lt_two (Q : ℝ) (h1 : 1 ≤ Q) (h2 : Q < 2) :
    |Work.LinnikAreas.Density4.selU Q - 1| ≤ (Real.log 4) ^ 3 * (Real.log (2 + Q)) ^ (-3 : ℤ) := by
  have hQ0 : (0:ℝ) < Q := lt_of_lt_of_le zero_lt_one h1
  have hQ2 : (0:ℝ) ≤ Q := le_of_lt hQ0
  -- `⌊Q⌋₊ = 1` since `1 ≤ Q < 2`
  have hfloor : ⌊Q⌋₊ = 1 := by
    rw [Nat.floor_eq_iff hQ2]
    exact ⟨by simpa using h1, by push_cast; linarith⟩
  -- the sum defining `selU` has the single term `m = 1`
  have hsel : Work.LinnikAreas.Density4.selU Q = Real.log Q := by
    unfold Work.LinnikAreas.Density4.selU
    rw [hfloor, Finset.Icc_self]
    simp
  rw [hsel]
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg h1
  have hlogQ1 : Real.log Q < 1 := by
    have h : Real.log Q < Real.log 2 := Real.log_lt_log hQ0 h2
    linarith [Real.log_two_lt_d9]
  have habs : |Real.log Q - 1| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  refine le_trans habs ?_
  -- the right-hand side is at least `1`
  have hpos : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
  have hle : Real.log (2 + Q) ≤ Real.log 4 := Real.log_le_log (by linarith) (by linarith)
  have hcube : (Real.log (2 + Q))^3 ≤ (Real.log 4)^3 :=
    pow_le_pow_left₀ (le_of_lt hpos) hle 3
  rw [zpow_neg, ← div_eq_mul_inv]
  exact (one_le_div (pow_pos hpos 3)).mpr hcube

end Work.LinnikAreas.Density4

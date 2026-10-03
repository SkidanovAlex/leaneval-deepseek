import Mathlib

namespace Work.Pert.V5

/-- Elementary logarithmic comparison: for `M ≥ 2^10`, `Ξ > 0` and
`0 ≤ L ≤ 16 * (M + 2 + Ξ)` we have `log (1 + L) ≤ 6 * (1 + Ξ) * (1 + log (2 + M))`.

The chain of estimates is
`log (1 + L) ≤ log (1 + 16 (M + 2 + Ξ)) ≤ log (17 (M + 2 + Ξ))`
`= log 17 + log (M + 2 + Ξ) ≤ log 17 + log (M + 2) + log (1 + Ξ) ≤ 5 + log (M + 2) + Ξ`,
and finally `5 + log (M + 2) + Ξ ≤ 6 (1 + Ξ) (1 + log (M + 2))`, since `log (M + 2) ≥ 0`. -/
theorem clear_log_bound {M Ξ L : ℝ} (hM : 2 ^ 10 ≤ M) (hΞ : 0 < Ξ) (hL : 0 ≤ L)
    (hlen : L ≤ 16 * (M + 2 + Ξ)) :
    Real.log (1 + L) ≤ 6 * (1 + Ξ) * (1 + Real.log (2 + M)) := by
  rw [show (2:ℝ) + M = M + 2 by ring]
  have hM1024 : (1024:ℝ) ≤ M := by norm_num at hM ⊢; exact hM
  -- `log (1 + L) ≤ log (1 + 16 (M + 2 + Ξ))`
  have hstep1 : Real.log (1 + L) ≤ Real.log (1 + 16 * (M + 2 + Ξ)) := by
    apply Real.log_le_log <;> linarith
  -- `1 + 16 (M + 2 + Ξ) ≤ 17 (M + 2 + Ξ)`
  have hstep2 : Real.log (1 + 16 * (M + 2 + Ξ)) ≤ Real.log (17 * (M + 2 + Ξ)) := by
    apply Real.log_le_log <;> linarith
  have hB : Real.log (17 * (M + 2 + Ξ)) = Real.log 17 + Real.log (M + 2 + Ξ) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
  -- `M + 2 + Ξ ≤ (M + 2) (1 + Ξ)`
  have hstep3 : Real.log (M + 2 + Ξ) ≤ Real.log ((M + 2) * (1 + Ξ)) := by
    apply Real.log_le_log <;> try nlinarith [hΞ, hM1024]
  have hC : Real.log ((M + 2) * (1 + Ξ)) = Real.log (M + 2) + Real.log (1 + Ξ) := by
    rw [Real.log_mul (by linarith) (by linarith)]
  -- `log (1 + Ξ) ≤ Ξ`
  have hstep4 : Real.log (1 + Ξ) ≤ Ξ := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + Ξ by linarith)
    linarith
  -- `log 17 ≤ 5`
  have h17 : Real.log 17 ≤ 5 := by
    have h1 : Real.log 17 ≤ Real.log 32 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log ((32:ℝ)) = 5 * Real.log 2 := by
      rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    linarith
  have hp : 0 ≤ Real.log (M + 2) := Real.log_nonneg (by linarith)
  have hfin : Real.log 17 + Real.log (M + 2) + Ξ ≤ 6 * (1 + Ξ) * (1 + Real.log (M + 2)) := by
    nlinarith [h17, hp, hΞ]
  have hchain : Real.log (1 + L) ≤ Real.log 17 + Real.log (M + 2) + Ξ := by
    linarith [hstep1, hstep2, hB, hstep3, hC, hstep4]
  linarith [hchain, hfin]

end Work.Pert.V5

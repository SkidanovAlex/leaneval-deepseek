import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiDefs

namespace Work.HP.MDEstimates.hiparts

theorem hiLZ_le_A_Q (B Δ M : ℝ) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 ≤ M) (hΔB : Δ ≤ B)
    (hQ : (2 * M) ^ 53 ≤ 2 * Δ) :
    hiLZ B (2 * Δ) (2 * M) ≤ 32 * 2 ^ 53 * B ^ 6 * Δ ^ 2 * M ^ 53 * (Real.log (4 * Δ)) ^ 2 := by
  have hBnn : (0 : ℝ) ≤ B := le_of_lt hB
  have hlog : Real.log (2 * (2 * Δ)) = Real.log (4 * Δ) := by
    rw [show 2 * (2 * Δ) = 4 * Δ by ring]
  -- Bound the `B`-part: `B^{9/2} (B^{3/2} + (2Δ)^{3/2}) ≤ 8 B^6`.
  have hstep : B ^ ((9 : ℝ) / 2) * (B ^ ((3 : ℝ) / 2) + (2 * Δ) ^ ((3 : ℝ) / 2))
      ≤ 8 * B ^ 6 := by
    have h3 : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 := by
      have h : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
      linarith
    have hq : (2 * Δ) ^ ((3 : ℝ) / 2) ≤ 4 * B ^ ((3 : ℝ) / 2) := by
      have h1 : (2 * Δ) ^ ((3 : ℝ) / 2) ≤ (2 * B) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      calc (2 * Δ) ^ ((3 : ℝ) / 2) ≤ (2 * B) ^ ((3 : ℝ) / 2) := h1
        _ = (2 : ℝ) ^ ((3 : ℝ) / 2) * B ^ ((3 : ℝ) / 2) := Real.mul_rpow (by norm_num) hBnn
        _ ≤ 4 * B ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hBnn _)
    have hB92 : (0 : ℝ) ≤ B ^ ((9 : ℝ) / 2) := Real.rpow_nonneg hBnn _
    have hcombine : B ^ ((9 : ℝ) / 2) * B ^ ((3 : ℝ) / 2) = B ^ 6 := by
      rw [← Real.rpow_add hB]
      norm_num
    calc B ^ ((9 : ℝ) / 2) * (B ^ ((3 : ℝ) / 2) + (2 * Δ) ^ ((3 : ℝ) / 2))
        ≤ B ^ ((9 : ℝ) / 2) * (B ^ ((3 : ℝ) / 2) + 4 * B ^ ((3 : ℝ) / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hB92; linarith
      _ = 5 * (B ^ ((9 : ℝ) / 2) * B ^ ((3 : ℝ) / 2)) := by ring
      _ = 5 * B ^ 6 := by rw [hcombine]
      _ ≤ 8 * B ^ 6 := by
          have : (0 : ℝ) ≤ B ^ 6 := pow_nonneg hBnn 6
          linarith
  have hZnn : (0 : ℝ) ≤ (2 * Δ) ^ 2 * (Real.log (4 * Δ)) ^ 2 * (2 * M) ^ 53 := by
    have h1 : (0 : ℝ) ≤ (2 * Δ) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (Real.log (4 * Δ)) ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ (2 * M) ^ 53 := pow_nonneg (by linarith) 53
    exact mul_nonneg (mul_nonneg h1 h2) h3
  unfold hiLZ
  rw [min_eq_right hQ, hlog]
  calc B ^ ((9 : ℝ) / 2) * (2 * Δ) ^ 2 * (B ^ ((3 : ℝ) / 2) + (2 * Δ) ^ ((3 : ℝ) / 2))
        * (Real.log (4 * Δ)) ^ 2 * (2 * M) ^ 53
      = (B ^ ((9 : ℝ) / 2) * (B ^ ((3 : ℝ) / 2) + (2 * Δ) ^ ((3 : ℝ) / 2)))
          * ((2 * Δ) ^ 2 * (Real.log (4 * Δ)) ^ 2 * (2 * M) ^ 53) := by ring
    _ ≤ (8 * B ^ 6) * ((2 * Δ) ^ 2 * (Real.log (4 * Δ)) ^ 2 * (2 * M) ^ 53) :=
          mul_le_mul_of_nonneg_right hstep hZnn
    _ = 32 * 2 ^ 53 * B ^ 6 * Δ ^ 2 * M ^ 53 * (Real.log (4 * Δ)) ^ 2 := by ring

end Work.HP.MDEstimates.hiparts

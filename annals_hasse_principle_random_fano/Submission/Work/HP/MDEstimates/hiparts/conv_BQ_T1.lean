import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiArithDefs

namespace Work.HP.MDEstimates.hiparts

/-- **Per-cell arithmetic, `B`,`Q` cell, first term.**
With `a = log A`, `b = log B`, `d = log Δ`, `m = log M`, the hypothesis is
`-5.96875 a + (6.501 + 1/1000) b - 2.5 d + 53 m ≤ 2000 - 59 log 2`, i.e.
`59 log 2 - 5.96875 a + 6.502 b - 2.5 d + 53 m ≤ 2000`.  Since
`32·2^53·B^{9/2+1/1000}·Δ^{7/2}·M^53·(A^62 B^4 Δ^{-6})
 = 2^58 A^62 B^{17/2+1/1000} Δ^{-5/2} M^53`
and `hiK/2·hiTgt A B = e^{2000}/2·A^{2175/32} B^{1999/1000}`, taking logarithms of both
sides reduces the claim to exactly the hypothesis (`62 - 2175/32 = -5.96875`,
`17/2 + 1/1000 - 1999/1000 = 6.502 = 6.501 + 1/1000`, `7/2 - 6 = -5/2`). -/
theorem conv_BQ_T1 (A B Δ M : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 < M)
    (h : -5.96875 * Real.log A + (6.501 + 1/1000) * Real.log B - 2.5 * Real.log Δ
        + 53 * Real.log M ≤ 2000 - 59 * Real.log 2) :
    32 * 2 ^ 53 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((7:ℝ)/2) * M ^ 53
        * (A ^ (62:ℝ) * B ^ (4:ℝ) * Δ ^ (-6:ℝ))
      ≤ hiK / 2 * hiTgt A B := by
  have hLpos : 0 < 32 * (2:ℝ) ^ 53 * B ^ ((9:ℝ)/2 + 1/1000) * Δ ^ ((7:ℝ)/2) * M ^ 53
      * (A ^ (62:ℝ) * B ^ (4:ℝ) * Δ ^ (-6:ℝ)) := by positivity
  have hRpos : 0 < hiK / 2 * hiTgt A B := by
    unfold hiK hiTgt; positivity
  rw [← Real.log_le_log_iff hLpos hRpos]
  have eL : Real.log (32 * (2:ℝ) ^ 53 * B ^ ((9:ℝ)/2 + 1/1000) * Δ ^ ((7:ℝ)/2) * M ^ 53
      * (A ^ (62:ℝ) * B ^ (4:ℝ) * Δ ^ (-6:ℝ)))
      = 58 * Real.log 2 + 62 * Real.log A + ((17:ℝ)/2 + 1/1000) * Real.log B
        - (5/2) * Real.log Δ + 53 * Real.log M := by
    rw [show (32:ℝ) = 2^5 by norm_num]
    rw [Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul]
    · rw [Real.log_pow, Real.log_pow, Real.log_pow, Real.log_rpow hB, Real.log_rpow hΔ,
        Real.log_rpow hA, Real.log_rpow hB, Real.log_rpow hΔ]
      ring
    all_goals positivity
  have eR : Real.log (hiK / 2 * hiTgt A B)
      = 2000 - Real.log 2 + (2175/32) * Real.log A + (1999/1000) * Real.log B := by
    unfold hiK hiTgt
    rw [Real.log_mul, Real.log_div, Real.log_mul, Real.log_rpow hA, Real.log_rpow hB, Real.log_exp]
    · ring
    all_goals positivity
  rw [eL, eR]
  linarith [h]

end Work.HP.MDEstimates.hiparts

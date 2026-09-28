import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiArithDefs

namespace Work.HP.MDEstimates.hiparts

/-- The exponents of the two monomials `L = 64 B^{6+1/1000} Δ³ (A^{68-k} B^{2k-8} Δ^{-k})` and
`R = hiK/2 * hiTgt A B = (e^{2000}/2) A^{2175/32} B^{1999/1000}` are aligned so that their
logarithms differ by exactly the quantity controlled by the hypothesis `h`:
`log L - log R = ((1/32-k) log A + (2k-3.999+1/1000) log B + (3-k) log Δ) - (2000 - log 128)`.
This is verified by taking logarithms of both sides and using `log 128 = log 64 + log 2`. -/
theorem conv_AP_T1 (A B Δ : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ) (k : ℕ) (hk : 4 ≤ k)
    (hk67 : k ≤ 67)
    (h : (1/32 - (k:ℝ)) * Real.log A + (2*(k:ℝ) - 3.999 + 1/1000) * Real.log B
        + (3 - (k:ℝ)) * Real.log Δ ≤ 2000 - Real.log 128) :
    64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3
        * (A ^ ((68:ℝ) - (k:ℝ)) * B ^ (2*(k:ℝ) - 8) * Δ ^ (-(k:ℝ)))
      ≤ hiK / 2 * hiTgt A B := by
  have hLpos : 0 < 64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3
        * (A ^ ((68:ℝ) - (k:ℝ)) * B ^ (2*(k:ℝ) - 8) * Δ ^ (-(k:ℝ))) := by positivity
  have hRpos : 0 < hiK / 2 * hiTgt A B := by
    have := hiK_pos; have := hiTgt_pos hA hB; positivity
  rw [← Real.log_le_log_iff hLpos hRpos]
  have hL : Real.log (64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3
        * (A ^ ((68:ℝ) - (k:ℝ)) * B ^ (2*(k:ℝ) - 8) * Δ ^ (-(k:ℝ))))
      = Real.log 64 + (6 + (1:ℝ)/1000) * Real.log B + 3 * Real.log Δ
        + (((68:ℝ) - (k:ℝ)) * Real.log A + (2*(k:ℝ) - 8) * Real.log B
            + (-(k:ℝ)) * Real.log Δ) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_rpow hB, Real.log_rpow hA, Real.log_rpow hB, Real.log_rpow hΔ]
    push_cast
    ring
  have hR : Real.log (hiK / 2 * hiTgt A B)
      = 2000 - Real.log 2 + ((2175:ℝ)/32 * Real.log A + (1999:ℝ)/1000 * Real.log B) := by
    unfold hiK hiTgt
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_div (by positivity) (by norm_num),
        Real.log_exp,
        Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hA, Real.log_rpow hB]
  rw [hL, hR]
  have h128 : Real.log 128 = Real.log 64 + Real.log 2 := by
    rw [show (128:ℝ) = 64 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hkey : (Real.log 64 + (6 + (1:ℝ)/1000) * Real.log B + 3 * Real.log Δ
        + (((68:ℝ) - (k:ℝ)) * Real.log A + (2*(k:ℝ) - 8) * Real.log B
            + (-(k:ℝ)) * Real.log Δ))
      - (2000 - Real.log 2 + ((2175:ℝ)/32 * Real.log A + (1999:ℝ)/1000 * Real.log B))
      = ((1/32 - (k:ℝ)) * Real.log A + (2*(k:ℝ) - 3.999 + 1/1000) * Real.log B
          + (3 - (k:ℝ)) * Real.log Δ) - (2000 - Real.log 128) := by
    rw [h128]; ring
  have hXY : (Real.log 64 + (6 + (1:ℝ)/1000) * Real.log B + 3 * Real.log Δ
        + (((68:ℝ) - (k:ℝ)) * Real.log A + (2*(k:ℝ) - 8) * Real.log B
            + (-(k:ℝ)) * Real.log Δ))
      - (2000 - Real.log 2 + ((2175:ℝ)/32 * Real.log A + (1999:ℝ)/1000 * Real.log B)) ≤ 0 := by
    rw [hkey]; linarith [h]
  linarith [hXY]

end Work.HP.MDEstimates.hiparts

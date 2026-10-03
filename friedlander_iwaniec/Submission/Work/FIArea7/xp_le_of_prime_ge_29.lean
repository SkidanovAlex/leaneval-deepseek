import Mathlib
import Submission.Work.FIArea7.MSmoothDefs

set_option autoImplicit false

namespace Work.FIArea7

/-- For a prime `p ≥ 29` the weight `xp p = p^{-1/4}` is at most `431/1000`.
Indeed `p ≥ 29 > (1000/431)^4`, so `p^{1/4} ≥ 1000/431` and hence
`p^{-1/4} ≤ 431/1000`. -/
lemma xp_le_of_prime_ge_29 (p : ℕ) (hp : p.Prime) (hp29 : 29 ≤ p) : xp p ≤ 431 / 1000 := by
  have hp29R : (29 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp29
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hbase : ((1000 / 431 : ℝ)) ^ (4 : ℝ) ≤ (p : ℝ) := by
    have h : ((1000 / 431 : ℝ)) ^ (4 : ℝ) ≤ (29 : ℝ) := by norm_num
    linarith
  have hA_nonneg : (0 : ℝ) ≤ ((1000 / 431 : ℝ)) ^ (4 : ℝ) := by positivity
  have hle : (((1000 / 431 : ℝ)) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) ≤ (p : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hA_nonneg hbase (by norm_num)
  have hleft : (((1000 / 431 : ℝ)) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = 1000 / 431 := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 1000 / 431 by norm_num)]
    norm_num
  have hle' : (1000 / 431 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← hleft]; exact hle
  have hp_pos' : (0 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hp_pos _
  calc xp p = ((p : ℝ) ^ ((1 : ℝ) / 4))⁻¹ := rfl
    _ ≤ (1000 / 431 : ℝ)⁻¹ := by
        rw [inv_le_inv₀ hp_pos' (by norm_num : (0 : ℝ) < 1000 / 431)]
        exact hle'
    _ = 431 / 1000 := by norm_num

end Work.FIArea7

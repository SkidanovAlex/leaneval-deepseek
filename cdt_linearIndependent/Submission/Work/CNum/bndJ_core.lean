import Mathlib
import Submission.Work.CNum.tD_aux

namespace Work.CNum

/-- Monotonicity in the modulus: the dominating bound `bndJ m` (built from `rJ = 79/100`)
dominates the same expression with any `e ≤ rJ`.  Used to transfer the second-derivative
bound from the arc `‖w ψ‖ ≤ rJ` to the actual value `e = ‖w ψ‖`. -/
theorem bndJ_core {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ rJ) {m : ℕ} (hm : 1 ≤ m) :
    24 * ((m : ℝ) * ((m : ℝ) - 1) * e ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m)
      + (m : ℝ) * e ^ (m - 1) * uJ / (1 - rJ ^ m)
      + (m : ℝ) ^ 2 * e ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2) ≤ bndJ m := by
  have hD : 0 < 1 - rJ ^ m := one_sub_rJ_pow_pos hm
  have hD0 : 0 ≤ 1 - rJ ^ m := le_of_lt hD
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have huJ0 : 0 ≤ uJ := uJ_nonneg
  have huJ02 : 0 ≤ uJ ^ 2 := sq_nonneg uJ
  have hep1 : e ^ (m - 2) ≤ rJ ^ (m - 2) := pow_le_pow_left₀ he0 he _
  have hep2 : e ^ (m - 1) ≤ rJ ^ (m - 1) := pow_le_pow_left₀ he0 he _
  have hep3 : e ^ (2 * m - 2) ≤ rJ ^ (2 * m - 2) := pow_le_pow_left₀ he0 he _
  have h1 : (m : ℝ) * ((m : ℝ) - 1) * e ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m)
      ≤ (m : ℝ) * ((m : ℝ) - 1) * rJ ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m) := by
    apply div_le_div_of_nonneg_right _ hD0
    calc (m : ℝ) * ((m : ℝ) - 1) * e ^ (m - 2) * uJ ^ 2
        = ((m : ℝ) * ((m : ℝ) - 1)) * (e ^ (m - 2) * uJ ^ 2) := by ring
      _ ≤ ((m : ℝ) * ((m : ℝ) - 1)) * (rJ ^ (m - 2) * uJ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hep1 huJ02)
            (mul_nonneg hm0 hm1)
      _ = (m : ℝ) * ((m : ℝ) - 1) * rJ ^ (m - 2) * uJ ^ 2 := by ring
  have h2 : (m : ℝ) * e ^ (m - 1) * uJ / (1 - rJ ^ m)
      ≤ (m : ℝ) * rJ ^ (m - 1) * uJ / (1 - rJ ^ m) := by
    apply div_le_div_of_nonneg_right _ hD0
    calc (m : ℝ) * e ^ (m - 1) * uJ = (m : ℝ) * (e ^ (m - 1) * uJ) := by ring
      _ ≤ (m : ℝ) * (rJ ^ (m - 1) * uJ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hep2 huJ0) hm0
      _ = (m : ℝ) * rJ ^ (m - 1) * uJ := by ring
  have h3 : (m : ℝ) ^ 2 * e ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2
      ≤ (m : ℝ) ^ 2 * rJ ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg (1 - rJ ^ m))
    calc (m : ℝ) ^ 2 * e ^ (2 * m - 2) * uJ ^ 2
        = ((m : ℝ) ^ 2) * (e ^ (2 * m - 2) * uJ ^ 2) := by ring
      _ ≤ ((m : ℝ) ^ 2) * (rJ ^ (2 * m - 2) * uJ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hep3 huJ02) (sq_nonneg _)
      _ = (m : ℝ) ^ 2 * rJ ^ (2 * m - 2) * uJ ^ 2 := by ring
  have hsum : (m : ℝ) * ((m : ℝ) - 1) * e ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m)
      + (m : ℝ) * e ^ (m - 1) * uJ / (1 - rJ ^ m)
      + (m : ℝ) ^ 2 * e ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2
      ≤ (m : ℝ) * ((m : ℝ) - 1) * rJ ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m)
      + (m : ℝ) * rJ ^ (m - 1) * uJ / (1 - rJ ^ m)
      + (m : ℝ) ^ 2 * rJ ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2 := by linarith
  have hfin := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 24)
  simpa [bndJ] using hfin

end Work.CNum

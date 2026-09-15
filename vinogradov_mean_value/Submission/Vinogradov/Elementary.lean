import ChallengeDeps
import Submission.Vinogradov.Asymptotic
import Submission.Vinogradov.Counting

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Vinogradov

noncomputable section
open Classical

/-- The theorem for `s = 0`: the empty system has a single solution. -/
theorem vmvt_s0 (k : ℕ) (ε : ℝ) (hε : 0 < ε) : VMVT 0 k ε hε := by
  dsimp [VMVT]
  refine Asymptotics.IsBigO.of_bound (1 : ℝ) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with X hX
  have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hJ : J 0 k X = 1 := J_eq_one_s0 k X
  have hone : (1 : ℝ) ≤ (X : ℝ) ^ ε := by
    simpa using (Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx1 (le_of_lt hε))
  have hle : (1 : ℝ) ≤ rhs 0 k ε X := by
    calc
      (1 : ℝ) ≤ (X : ℝ) ^ ε := hone
      _ ≤ rhs 0 k ε X := by
        -- rhs ≥ its first summand X^((0 : ℕ) + ε)
        calc
          (X : ℝ) ^ ε = (X : ℝ) ^ (((0 : ℕ) : ℝ) + ε) := by congr 1; norm_num
          _ ≤ rhs 0 k ε X := rhs_ge_first 0 k ε X
  rw [hJ]
  have hJ0 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  have hR0 : 0 ≤ rhs 0 k ε X := rhs_nonneg 0 k ε X
  rw [Real.norm_of_nonneg hJ0, Real.norm_of_nonneg hR0]
  simpa using hle

/-- The theorem for `k = 0`: no equations means all pairs count. -/
theorem vmvt_k0 (s : ℕ) (ε : ℝ) (hε : 0 < ε) : VMVT s 0 ε hε := by
  dsimp [VMVT]
  refine Asymptotics.IsBigO.of_bound (1 : ℝ) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with X hX
  have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hJ : J s 0 X ≤ (↑((X ^ s) ^ 2) : ℝ) := J_le_card s 0 X
  have hsq : ((X ^ s) ^ 2 : ℕ) = X ^ (2 * s) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hsq] at hJ
  have hle : J s 0 X ≤ rhs s 0 ε X := by
    refine hJ.trans ?_
    have hstep : (↑(X ^ (2 * s)) : ℝ) ≤ (X : ℝ) ^ ((2 * s : ℝ) + ε) := by
      calc
        (↑(X ^ (2 * s)) : ℝ) = (X : ℝ) ^ (((2 * s : ℕ) : ℝ)) := by
          rw [Real.rpow_natCast]; norm_num
        _ ≤ (X : ℝ) ^ ((2 * s : ℝ) + ε) := by
          apply Real.rpow_le_rpow_of_exponent_le hx1
          norm_num
          linarith
    refine hstep.trans ?_
    exact (by
      -- rhs ≥ its second summand X^((2s) - 0·1/2 + ε), and the exponents agree
      have hE : (2 * s : ℝ) + ε = (2 * s : ℝ) - (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + 1)) / 2 + ε := by
        norm_num
      rw [hE]
      exact rhs_ge_second s 0 ε X)
  have hJ0 : 0 ≤ J s 0 X := J_nonneg s 0 X
  have hR0 : 0 ≤ rhs s 0 ε X := rhs_nonneg s 0 ε X
  rw [Real.norm_of_nonneg hJ0, Real.norm_of_nonneg hR0]
  simpa using hle

/-- For `k = 1` and `s = m + 1 ≥ 1`. -/
theorem vmvt_k1_succ (m : ℕ) (ε : ℝ) (hε : 0 < ε) : VMVT (m + 1) 1 ε hε := by
  dsimp [VMVT]
  refine Asymptotics.IsBigO.of_bound (1 : ℝ) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with X hX
  have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hJ : J (m + 1) 1 X ≤ (↑(X ^ (2 * m + 1)) : ℝ) := by exact_mod_cast J_le_pow_k1 m X
  have hle : J (m + 1) 1 X ≤ rhs (m + 1) 1 ε X := by
    refine hJ.trans ?_
    have hstep : (↑(X ^ (2 * m + 1)) : ℝ) ≤ (X : ℝ) ^ (((2 * m + 1 : ℕ) : ℝ) + ε) := by
      calc
        (↑(X ^ (2 * m + 1)) : ℝ) = (X : ℝ) ^ (((2 * m + 1 : ℕ) : ℝ)) := by
          rw [Real.rpow_natCast]; norm_num
        _ ≤ (X : ℝ) ^ (((2 * m + 1 : ℕ) : ℝ) + ε) := by
          apply Real.rpow_le_rpow_of_exponent_le hx1
          linarith
    refine hstep.trans ?_
    exact (by
      have hAB : ((2 * m + 1 : ℕ) : ℝ) + ε ≤ (2 * ((m + 1 : ℕ) : ℝ)) - (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) + 1)) / 2 + ε := by
        norm_num
        linarith
      exact (Real.rpow_le_rpow_of_exponent_le hx1 hAB).trans (rhs_ge_second (m + 1) 1 ε X))
  have hJ0 : 0 ≤ J (m + 1) 1 X := J_nonneg (m + 1) 1 X
  have hR0 : 0 ≤ rhs (m + 1) 1 ε X := rhs_nonneg (m + 1) 1 ε X
  rw [Real.norm_of_nonneg hJ0, Real.norm_of_nonneg hR0]
  simpa using hle

/-- The theorem for `k = 1`: solutions of a single linear equation are at most
`X^(2s-1)`, the sharp exponent. -/
theorem vmvt_k1 (s : ℕ) (ε : ℝ) (hε : 0 < ε) : VMVT s 1 ε hε := by
  by_cases hs : s = 0
  · subst s
    exact vmvt_s0 1 ε hε
  · have hs' : (s - 1) + 1 = s := by omega
    have hsucc := vmvt_k1_succ (s - 1) ε hε
    rwa [hs'] at hsucc

end
end Submission.Vinogradov

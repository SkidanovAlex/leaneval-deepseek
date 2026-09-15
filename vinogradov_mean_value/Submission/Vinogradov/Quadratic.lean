import ChallengeDeps
import Submission.Vinogradov.Core
import Submission.Vinogradov.Asymptotic
import Submission.Vinogradov.ShortMoments
import Submission.Commons.Combinatorics.Fin.quadratic_mean_value_bound
import Submission.Commons.Analysis.ExpLog.log_absorption

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Vinogradov

noncomputable section
open Classical

/-- The `k = 2` (quadratic) case of the Vinogradov mean value theorem:
`J s 2 X ≪ X^(2s-3+ε)` for `s ≥ 3` (and `s ≤ 2` handled by the short-moments
regime; at `s = 3` there is a logarithm which the `X^ε` absorbs). -/
theorem vmvt_k2 (s : ℕ) (ε : ℝ) (hε : 0 < ε) : VMVT s 2 ε hε := by
  by_cases hs2 : s ≤ 2
  · exact vmvt_short s 2 hs2 ε hε
  · have hs3 : 3 ≤ s := by omega
    rcases (Commons.Combinatorics.Fin.quadratic_mean_value_bound s hs3) with ⟨C, hC0, hC⟩
    rcases (Commons.Analysis.ExpLog.log_absorption hε) with ⟨D, hD0, hD⟩
    let K : ℝ := C * D
    have hK0 : 0 < K := mul_pos hC0 hD0
    dsimp [VMVT]
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with X hX
    have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hx0 : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast Nat.zero_le X
    have hxp : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le zero_lt_one hx1
    have hJ1 : J s 2 X ≤ C * (X : ℝ) ^ (2 * s - 3 : ℕ) * (1 + Real.log ((X : ℝ) + 1)) := by
      rw [J_eq_filter_card]
      have hfilter :
          (Finset.univ.filter (Matches s 2 X)) =
            (Finset.univ.filter (fun xy : PairSpace s X =>
              (∑ i, (xy.1 i).1) = (∑ i, (xy.2 i).1) ∧
              (∑ i, ((xy.1 i).1) ^ 2) = (∑ i, ((xy.2 i).1) ^ 2))) := by
        ext xy
        simp [Matches]
        constructor
        · intro h
          constructor
          · simpa using (h 1 (by omega))
          · simpa using (h 2 (by omega))
        · intro h j hj
          have hj02 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
          rcases hj02 with rfl | rfl | rfl
          · simp
          · simpa using h.1
          · exact h.2
      rw [hfilter]
      exact hC X hX
    have habs : (1 + Real.log ((X : ℝ) + 1)) ≤ D * (X : ℝ) ^ ε := hD (X : ℝ) hx1
    have hJ2 : J s 2 X ≤ K * (X : ℝ) ^ ((2 * s : ℝ) - 3 + ε) := by
      calc
        J s 2 X ≤ C * (X : ℝ) ^ (2 * s - 3 : ℕ) * (1 + Real.log ((X : ℝ) + 1)) := hJ1
        _ ≤ C * (X : ℝ) ^ (2 * s - 3 : ℕ) * (D * (X : ℝ) ^ ε) := by
          exact mul_le_mul_of_nonneg_left habs (mul_nonneg (le_of_lt hC0) (pow_nonneg hx0 _))
        _ = (C * D) * ((X : ℝ) ^ (2 * s - 3 : ℕ) * (X : ℝ) ^ ε) := by ring
        _ ≤ K * (X : ℝ) ^ (((2 * s - 3 : ℕ) : ℝ) + ε) := by
          -- X^(2s-3) * X^ε ≤ X^((2s-3)+ε) by rpow_add
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hK0)
          have hprod : (X : ℝ) ^ (2 * s - 3 : ℕ) * (X : ℝ) ^ ε = (X : ℝ) ^ (((2 * s - 3 : ℕ) : ℝ) + ε) := by
            rw [← Real.rpow_natCast]
            exact (Real.rpow_add hxp _ _).symm
          rw [hprod]
        _ ≤ K * (X : ℝ) ^ ((2 * s : ℝ) - 3 + ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hK0)
          apply Real.rpow_le_rpow_of_exponent_le hx1
          -- (((2s-3:ℕ):ℝ)+ε) ≤ (2s:ℝ)-3+ε, since 3 ≤ 2s
          have hs3n : 3 ≤ 2 * s := by omega
          rw [Nat.cast_sub hs3n]
          norm_num [Nat.cast_mul, Nat.cast_ofNat]
    have hle : J s 2 X ≤ K * rhs s 2 ε X := by
      calc
        J s 2 X ≤ K * (X : ℝ) ^ ((2 * s : ℝ) - 3 + ε) := hJ2
        _ ≤ K * rhs s 2 ε X := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hK0)
          have hAB : (2 * s : ℝ) - 3 + ε ≤ (2 * s : ℝ) - (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) + 1)) / 2 + ε := by
            norm_num
          exact (Real.rpow_le_rpow_of_exponent_le hx1 hAB).trans (rhs_ge_second s 2 ε X)
    have hJ0 : 0 ≤ J s 2 X := J_nonneg s 2 X
    have hR0 : 0 ≤ rhs s 2 ε X := rhs_nonneg s 2 ε X
    rw [Real.norm_of_nonneg hJ0, Real.norm_of_nonneg hR0]
    exact hle

end
end Submission.Vinogradov

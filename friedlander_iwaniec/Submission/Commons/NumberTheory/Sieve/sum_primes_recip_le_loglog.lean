import Mathlib
import Submission.Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log

open scoped BigOperators

namespace Commons.NumberTheory.Sieve

/-- For `k ∈ {2,3}`, `log (log k) ≥ -1`.  This handles the small values of `N`
in the main statement, where `log log N` can be (slightly) negative. -/
private lemma log_log_ge_neg_one_of_small {k : ℕ} (hk2 : 2 ≤ k) (hk3 : k ≤ 3) :
    -1 ≤ Real.log (Real.log (k : ℝ)) := by
  interval_cases k
  · have hlog2_half : (1 / 2 : ℝ) ≤ Real.log 2 := by nlinarith [Real.log_two_gt_d9]
    have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    have hle : Real.log (1 / 2 : ℝ) ≤ Real.log (Real.log 2) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlog2_half
    have hminus : -1 ≤ Real.log (1 / 2 : ℝ) := by
      rw [hlog_half]; nlinarith [Real.log_two_lt_d9]
    exact le_trans hminus hle
  · have hlog3_half : (1 / 2 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
      linarith [Real.log_two_gt_d9]
    have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    have hle : Real.log (1 / 2 : ℝ) ≤ Real.log (Real.log 3) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlog3_half
    have hminus : -1 ≤ Real.log (1 / 2 : ℝ) := by
      rw [hlog_half]; nlinarith [Real.log_two_lt_d9]
    exact le_trans hminus hle

/-- Euler–Mertens (second Mertens theorem) upper bound: the sum of `1/p` over the
primes `p < N` is at most `log (log N) + C` for an absolute constant `C`. -/
theorem sum_primes_recip_le_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p) ≤ Real.log (Real.log N) + C := by
  obtain ⟨C, hC0, hC⟩ :=
    Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log
  refine ⟨C + 2, by linarith, ?_⟩
  intro N hN
  by_cases h4 : 4 ≤ N
  · -- large `N`: reduce to the published bound at `N - 1`, using monotonicity of `log log`.
    have hN1 : 3 ≤ N - 1 := by omega
    have hb := hC (N - 1) hN1
    rw [show (N - 1) + 1 = N by omega] at hb
    have hpos : 0 < ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < N - 1)
    have hcast : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (by omega : N - 1 ≤ N)
    have hlogpos : 0 < Real.log ((N - 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < N - 1))
    have hmono : Real.log (Real.log ((N - 1 : ℕ) : ℝ)) ≤ Real.log (Real.log (N : ℝ)) :=
      Real.log_le_log hlogpos (Real.log_le_log hpos hcast)
    linarith
  · -- small `N ∈ {2,3}`: the sum is at most `1`, and `log log N ≥ -1`.
    have hsmall : -1 ≤ Real.log (Real.log (N : ℝ)) :=
      log_log_ge_neg_one_of_small hN (by omega)
    have hsum_le : (∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p) ≤ 1 := by
      interval_cases N
      · simp
      · rw [show Nat.primesBelow 3 = ({2} : Finset ℕ) by decide]
        norm_num
    linarith

end Commons.NumberTheory.Sieve

import Mathlib
import Submission.Commons.NumberTheory.Mertens.first_mertens_bounded
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_div_p_mul_pred_le_one

namespace Commons.NumberTheory.Mertens

open scoped BigOperators

/-- Termwise splitting for a prime `p ≥ 2`:
`log p / (p - 1) = log p / p + log p / (p (p - 1))`. -/
private lemma log_div_pred_eq_split {p : ℕ} (hp : p.Prime) :
    Real.log (p : ℝ) / ((p : ℝ) - 1)
      = Real.log (p : ℝ) / (p : ℝ)
        + Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **Sharp first Mertens theorem for `log p / (p - 1)`.**
There is an absolute constant `A > 0` such that
`|Σ_{p ≤ y} log p / (p - 1) − log y| ≤ A` for every `y ≥ 2`. -/
theorem sum_log_div_le_log_sharp : ∃ A : ℝ, 0 < A ∧ ∀ y : ℕ, 2 ≤ y →
    |(∑ p ∈ (Nat.primesLE y).filter (fun p : ℕ => 2 ≤ p), Real.log (p : ℝ) / ((p : ℝ) - 1)) - Real.log (y : ℝ)| ≤ A := by
  -- `|logDiv x - log x|` is bounded by an absolute constant.
  rcases first_mertens_bounded with ⟨C, hCpos, hC⟩
  refine ⟨C + 1, by positivity, ?_⟩
  intro y hy
  -- The filter `2 ≤ p` is vacuous on primes `≤ y`.
  have hfilter : (Nat.primesLE y).filter (fun p : ℕ => 2 ≤ p) = Nat.primesLE y := by
    apply Finset.filter_true_of_mem
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2.two_le
  rw [hfilter]
  -- The correction sum `Σ log p / (p (p - 1))`, bounded in `[0, 1]`.
  set T : ℝ := ∑ p ∈ Nat.primesLE y, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) with hTdef
  -- Split each summand.
  have hsplit : (∑ p ∈ Nat.primesLE y, Real.log (p : ℝ) / ((p : ℝ) - 1))
      = (∑ p ∈ Nat.primesLE y, Real.log (p : ℝ) / (p : ℝ)) + T := by
    rw [hTdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p hp => log_div_pred_eq_split (Nat.mem_primesLE.mp hp).2)
  -- `logDiv` at the integer `y` is exactly `Σ_{p ≤ y} log p / p`.
  have hmainsum : logDiv (y : ℝ) = ∑ p ∈ Nat.primesLE y, Real.log (p : ℝ) / (p : ℝ) := by
    unfold logDiv
    simp
  have hTnonneg : 0 ≤ T := by
    rw [hTdef]
    refine Finset.sum_nonneg (fun p hp => ?_)
    have hpp : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    exact div_nonneg hlog (mul_nonneg (by linarith) (by linarith))
  have hTle : T ≤ 1 := by
    rw [hTdef]
    exact sum_log_prime_div_p_mul_pred_le_one y
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hM : |logDiv (y : ℝ) - Real.log (y : ℝ)| ≤ C := hC (y : ℝ) hyR
  -- Rewrite the target difference as `(logDiv y − log y) + T`.
  have hkey : (∑ p ∈ Nat.primesLE y, Real.log (p : ℝ) / ((p : ℝ) - 1)) - Real.log (y : ℝ)
      = (logDiv (y : ℝ) - Real.log (y : ℝ)) + T := by
    rw [hsplit, hmainsum]
    ring
  rw [hkey]
  calc
    |(logDiv (y : ℝ) - Real.log (y : ℝ)) + T|
        ≤ |logDiv (y : ℝ) - Real.log (y : ℝ)| + |T| := abs_add_le _ _
    _ ≤ C + 1 := by
          rw [abs_of_nonneg hTnonneg]
          linarith

end Commons.NumberTheory.Mertens

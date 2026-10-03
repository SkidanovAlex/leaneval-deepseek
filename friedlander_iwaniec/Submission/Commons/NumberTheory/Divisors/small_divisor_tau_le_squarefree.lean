import Mathlib
import Submission.Commons.NumberTheory.Sieve.squarefree_dvd_le_rpow_tau_le

namespace Commons.NumberTheory.Divisors

/-- For squarefree `n ≥ 1` and `k ≥ 2`, some divisor `d ∣ n` with `d ^ k ≤ n` already
captures the divisor count of `n`: `τ(n) ≤ (2 τ(d)) ^ k`.  The natural-number form is
`Commons.NumberTheory.Sieve.squarefree_dvd_le_rpow_tau_le`; here we cast it to `ℝ`. -/
theorem small_divisor_tau_le_squarefree {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) (hsf : Squarefree n) :
    ∃ d : ℕ, d ∣ n ∧ d ^ k ≤ n ∧ (n.divisors.card : ℝ) ≤ (2 * (d.divisors.card : ℝ)) ^ (k : ℝ) := by
  obtain ⟨d, hdvd, hdpow, hdcard⟩ :=
    Commons.NumberTheory.Sieve.squarefree_dvd_le_rpow_tau_le n k hk hsf hn
  refine ⟨d, hdvd, hdpow, ?_⟩
  have h1 : ((n.divisors.card : ℕ) : ℝ) ≤ ((2 * d.divisors.card : ℕ) : ℝ) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hdcard
  rwa [Nat.cast_mul, Nat.cast_ofNat] at h1

end Commons.NumberTheory.Divisors

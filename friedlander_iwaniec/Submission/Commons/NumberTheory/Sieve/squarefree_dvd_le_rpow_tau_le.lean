import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_bound_of_squarefree

namespace Commons.NumberTheory.Sieve

/-- **Lemma 1 of the companion paper "Asymptotic sieve for primes"** (corrected form):
a squarefree `n ≥ 1` has a divisor `d ≤ n ^ (1/k)` whose divisor count already captures
that of `n` up to the factor `(2·τ(d)) ^ k`, i.e. `τ(n) ≤ (2 τ(d)) ^ k`.
(Concretely `d` is the product of the `⌊ω(n)/k⌋` smallest prime factors of `n`.) -/
theorem squarefree_dvd_le_rpow_tau_le (n k : ℕ) (hk : 2 ≤ k) (hn : Squarefree n) (h1 : 1 ≤ n) :
    ∃ d : ℕ, d ∣ n ∧ d ^ k ≤ n ∧ (Nat.divisors n).card ≤ (2 * (Nat.divisors d).card) ^ k := by
  rcases eq_or_lt_of_le h1 with h | h
  · -- n = 1 : take d = 1
    rw [← h]
    refine ⟨1, one_dvd 1, by simp, ?_⟩
    rw [Nat.divisors_one]
    simp only [Finset.card_singleton, mul_one]
    exact Nat.one_le_pow k 2 (by norm_num)
  · -- 1 < n : apply the already-proven commons lemma
    exact Commons.NumberTheory.FriedlanderIwaniec.tau_bound_of_squarefree h hn
      (le_trans (by norm_num : (1 : ℕ) ≤ 2) hk)

end Commons.NumberTheory.Sieve

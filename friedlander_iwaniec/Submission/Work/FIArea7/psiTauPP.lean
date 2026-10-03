import Mathlib

namespace Work.FIArea7

/-- For a non-prime prime power `m = p^k` (`k ≥ 2`) with `m ≤ L`, `τ(m) = k + 1 ≤ log₂ L + 1`. -/
theorem psiTauPP {m L : ℕ} (hm : IsPrimePow m) (hmL : m ≤ L) (hmp : ¬ m.Prime) :
    m.divisors.card ≤ Nat.log 2 L + 1 := by
  -- `hmp` is part of the hypothesis but the bound in fact holds for every prime power.
  have _ := hmp
  obtain ⟨p, k, hp, hk, hpk⟩ := hm
  have hpprime : Nat.Prime p := hp.nat_prime
  -- the number of divisors of a prime power `p^k` is exactly `k + 1`
  have hcard : m.divisors.card = k + 1 := by
    rw [← hpk, Nat.divisors_prime_pow hpprime k]
    simp
  rw [hcard]
  -- `2^k ≤ p^k = m ≤ L`, hence `k ≤ log₂ L`
  have h2k : 2 ^ k ≤ L := by
    have hle : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hpprime.two_le k
    rw [hpk] at hle
    exact le_trans hle hmL
  have hlog : k ≤ Nat.log 2 L := Nat.le_log_of_pow_le (by norm_num) h2k
  omega

end Work.FIArea7

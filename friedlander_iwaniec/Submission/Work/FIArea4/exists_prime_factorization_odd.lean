import Mathlib

namespace Work.FIArea4

/-- If `n ≠ 0` is not a perfect square, then some prime occurs in `n` to an odd power. -/
theorem exists_prime_factorization_odd (n : ℕ) (hn : n ≠ 0)
    (hnsq : ∀ k : ℕ, n ≠ k ^ 2) :
    ∃ p : ℕ, p.Prime ∧ Odd (n.factorization p) := by
  -- We argue by contradiction: if every prime exponent were even, `n` would be a square.
  by_contra h
  push Not at h
  -- Every prime occurring in `n` occurs to an even power.
  have hfac : ∀ p ∈ n.primeFactors, n.factorization p = 2 * (n.factorization p / 2) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hev : Even (n.factorization p) := by
      rcases Nat.even_or_odd (n.factorization p) with he | ho
      · exact he
      · exact absurd ho (h p hpp)
    exact (Nat.two_mul_div_two_of_even hev).symm
  -- Hence `n = (∏ p, p^(e_p/2))^2` is a perfect square.
  have hprod : (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2
      = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p hp
    conv_rhs => rw [hfac p hp, mul_comm 2 (n.factorization p / 2), pow_mul]
  exact hnsq _ ((hprod.trans (Nat.prod_primeFactors_pow_factorization hn).symm).symm)

end Work.FIArea4

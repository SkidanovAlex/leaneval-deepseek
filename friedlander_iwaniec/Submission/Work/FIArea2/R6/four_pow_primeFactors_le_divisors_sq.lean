import Mathlib

namespace Work.FIArea2.R6

/-- `4 ^ ω(m) ≤ τ(m) ^ 2` for `m > 0`: `τ(m) = ∏_{p ∣ m} (v_p(m) + 1) ≥ ∏ 2 = 2 ^ ω(m)`. -/
theorem four_pow_primeFactors_le_divisors_sq (m : ℕ) (hm : 0 < m) :
    4 ^ m.primeFactors.card ≤ m.divisors.card ^ 2 := by
  -- `2 ^ ω(m) ≤ τ(m)`: each factor `v_p(m) + 1` of the divisor-count product is at least `2`.
  have h2 : 2 ^ m.primeFactors.card ≤ m.divisors.card := by
    rw [Nat.card_divisors (ne_of_gt hm),
      ← Finset.prod_const (s := m.primeFactors) (2 : ℕ)]
    apply Finset.prod_le_prod₀
    · intro i _; norm_num
    · intro i hi
      obtain ⟨hp, hd, -⟩ := Nat.mem_primeFactors.mp hi
      have h1 : 1 ≤ m.factorization i :=
        (hp.dvd_iff_one_le_factorization (ne_of_gt hm)).mp hd
      omega
  -- `4 ^ ω(m) = (2 ^ ω(m)) ^ 2`.
  have h4 : 4 ^ m.primeFactors.card = (2 ^ m.primeFactors.card) ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul,
      Nat.mul_comm 2 m.primeFactors.card]
  rw [h4]
  exact pow_le_pow_left₀ (Nat.zero_le _) h2 2

end Work.FIArea2.R6

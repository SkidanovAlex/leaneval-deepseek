import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Chebyshev
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_even_dvd_binom_mul

namespace Commons.NumberTheory.Chebyshev

/-- For `q ≥ 2` and any `m`, the sum of the residues of two consecutive numbers
`m`, `m + 1` modulo `q` is at most `2 * q - 3`. -/
lemma mod_add_mod_succ_le (m q : ℕ) (hq : 2 ≤ q) :
    m % q + (m + 1) % q ≤ 2 * q - 3 := by
  have h1 : (m + 1) % q = (m % q + 1) % q := by
    rw [Nat.add_mod]; simp
  rw [h1]
  have hlt : m % q < q := Nat.mod_lt _ (by omega)
  rcases lt_or_eq_of_le (show m % q + 1 ≤ q by omega) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [h, Nat.mod_self]; omega

/-- Integer-division form of the key estimate: for `q ≥ 2`,
`(2n - 1) / q ≤ (n - 2) / q + (n - 1) / q + 1`. -/
lemma div_two_mul_sub_one_le (n q : ℕ) (hq : 2 ≤ q) :
    (2 * n - 1) / q ≤ (n - 2) / q + (n - 1) / q + 1 := by
  have hqpos : 0 < q := by omega
  rw [Nat.div_le_iff_le_mul_add_pred hqpos]
  have hres : (n - 2) % q + (n - 1) % q ≤ 2 * q - 3 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn2 : n - 2 = 0 := by omega
      have hn1 : n - 1 = 0 := by omega
      rw [hn2, hn1]
      simp only [Nat.zero_mod, zero_add]
      omega
    · have hstep : n - 1 = (n - 2) + 1 := by omega
      rw [hstep]
      exact mod_add_mod_succ_le (n - 2) q hq
  have hA := Nat.div_add_mod (n - 2) q
  have hB := Nat.div_add_mod (n - 1) q
  have e1 : q * ((n - 2) / q) = n - 2 - (n - 2) % q := by omega
  have e2 : q * ((n - 1) / q) = n - 1 - (n - 1) % q := by omega
  have expand : q * ((n - 2) / q + (n - 1) / q + 1)
      = q * ((n - 2) / q) + q * ((n - 1) / q) + q := by ring
  rw [expand, e1, e2]
  omega

/-- `(2n-1)!` divides `lcmUpto (2n) * (n-2)! * (n-1)!`. -/
lemma factorial_two_mul_sub_one_dvd (n : ℕ) (hn : 1 ≤ n) :
    (2 * n - 1).factorial ∣ Nat.lcmUpto (2 * n) * (n - 2).factorial * (n - 1).factorial := by
  have hL : Nat.lcmUpto (2 * n) ≠ 0 := Nat.lcmUpto_ne_zero _
  have h2 : (n - 2).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h3 : (n - 1).factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.factorial_ne_zero _)
      (Nat.mul_ne_zero (Nat.mul_ne_zero hL h2) h3)]
  intro p hp
  set B := Nat.log p (2 * n) + 1 with hB
  have hlog1 : Nat.log p (2 * n - 1) < B := by
    have := Nat.log_mono_right (b := p) (show 2 * n - 1 ≤ 2 * n by omega); omega
  have hlog2 : Nat.log p (n - 2) < B := by
    have := Nat.log_mono_right (b := p) (show n - 2 ≤ 2 * n by omega); omega
  have hlog3 : Nat.log p (n - 1) < B := by
    have := Nat.log_mono_right (b := p) (show n - 1 ≤ 2 * n by omega); omega
  rw [Nat.factorization_factorial hp hlog1,
      Nat.factorization_mul (Nat.mul_ne_zero hL h2) h3, Finsupp.add_apply,
      Nat.factorization_mul hL h2, Finsupp.add_apply,
      Nat.factorization_lcmUpto (2 * n) hp,
      Nat.factorization_factorial hp hlog2,
      Nat.factorization_factorial hp hlog3]
  have hcard : (Finset.Ico 1 B).card = Nat.log p (2 * n) := by
    rw [Nat.card_Ico]; omega
  calc (∑ i ∈ Finset.Ico 1 B, (2 * n - 1) / p ^ i)
      ≤ ∑ i ∈ Finset.Ico 1 B, ((n - 2) / p ^ i + (n - 1) / p ^ i + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
        have hq : 2 ≤ p ^ i := by
          calc 2 ≤ p := hp.two_le
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ i := pow_le_pow_right₀ (le_of_lt hp.one_lt) hi1
        exact div_two_mul_sub_one_le n (p ^ i) hq
    _ = (Nat.log p (2 * n) + ∑ i ∈ Finset.Ico 1 B, (n - 2) / p ^ i)
          + ∑ i ∈ Finset.Ico 1 B, (n - 1) / p ^ i := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard]
        simp
        ring

theorem dvd_lcmUpto_fact_two_mul_sub_one_mul_fact_div (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (Nat.lcmUpto (2 * n) : ℚ) * ((((n - 2).factorial : ℚ)) * (((n - 1).factorial : ℚ)))
        / (((2 * n - 1).factorial : ℚ)) = (z : ℚ) := by
  obtain ⟨q, hq⟩ := factorial_two_mul_sub_one_dvd n hn
  refine ⟨(q : ℤ), ?_⟩
  have hD : (((2 * n - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n - 1)
  have hcast : ((Nat.lcmUpto (2 * n) * (n - 2).factorial * (n - 1).factorial : ℕ) : ℚ)
      = ((2 * n - 1).factorial : ℚ) * (q : ℚ) := by
    rw [hq]; push_cast; ring
  have hprod : (Nat.lcmUpto (2 * n) : ℚ) *
        (((n - 2).factorial : ℚ) * ((n - 1).factorial : ℚ))
      = ((Nat.lcmUpto (2 * n) * (n - 2).factorial * (n - 1).factorial : ℕ) : ℚ) := by
    push_cast; ring
  rw [hprod, hcast, mul_div_cancel_left₀ _ hD]
  simp

end Commons.NumberTheory.Chebyshev
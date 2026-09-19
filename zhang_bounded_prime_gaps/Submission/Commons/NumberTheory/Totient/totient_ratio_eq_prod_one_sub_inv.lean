import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Totient
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_card_divisors_pow_div_totient_le_uniform

open scoped BigOperators

namespace Commons.NumberTheory.Totient

/-- Totient density as an Euler product over the distinct prime factors:
for `n ≠ 0`, `φ(n)/n = ∏_{p | n} (1 − 1/p)` in `ℚ`. -/
theorem totient_ratio_eq_prod_one_sub_inv (n : ℕ) (hn : n ≠ 0) :
    ((Nat.totient n : ℚ) / (n : ℚ)) =
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ)) := by
  classical
  -- Euler's product formula over ℕ:
  --   φ n * ∏_{p | n} p = n * ∏_{p | n} (p - 1)
  -- (`Nat.totient_mul_prod_primeFactors`); cast it to ℚ.
  have hQ :
      (Nat.totient n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ) =
        (n : ℚ) * ∏ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℚ)) := by
    have hmain := Nat.totient_mul_prod_primeFactors n
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) hmain
    simpa [Nat.cast_mul, Nat.cast_prod] using hcast
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  have hP0 : (∏ p ∈ n.primeFactors, (p : ℚ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact_mod_cast (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  calc
    (Nat.totient n : ℚ) / (n : ℚ)
        = (∏ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℚ))) /
            ∏ p ∈ n.primeFactors, (p : ℚ) := by
          field_simp [hnQ, hP0]
          exact hQ
    _ = ∏ p ∈ n.primeFactors, ((((p - 1 : ℕ) : ℚ) / (p : ℚ))) := by
          rw [Finset.prod_div_distrib]
    _ = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ)) := by
          apply Finset.prod_congr rfl
          intro p hp
          have hpne : (p : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
          have hsub : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
            exact (Nat.cast_sub (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)))
          rw [hsub]
          field_simp [hpne]

end Commons.NumberTheory.Totient
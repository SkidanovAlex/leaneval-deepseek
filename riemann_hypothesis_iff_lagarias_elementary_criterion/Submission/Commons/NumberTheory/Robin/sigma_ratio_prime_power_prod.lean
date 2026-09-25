import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped BigOperators

namespace Commons.NumberTheory.Robin

/-- For a prime power `p ^ k`, the ratio `σ 1 (p ^ k) / p ^ k` (as real numbers) is the
closed-form geometric sum `(p ^ (k + 1) - 1) / (p ^ k * (p - 1))`. -/
lemma sigma_one_ratio_prime_pow {p k : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.sigma 1 (p ^ k) : ℕ) : ℝ) / ((p : ℝ) ^ k) =
      ((p : ℝ) ^ (k + 1) - 1) / (((p : ℝ) ^ k) * ((p : ℝ) - 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (Nat.Prime.ne_one hp)
  have hσ : ArithmeticFunction.sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    simpa using (ArithmeticFunction.sigma_one_apply_prime_pow (i := k) hp)
  calc
    ((ArithmeticFunction.sigma 1 (p ^ k) : ℕ) : ℝ) / ((p : ℝ) ^ k)
        = (∑ i ∈ Finset.range (k + 1), (p : ℝ) ^ i) / ((p : ℝ) ^ k) := by
            rw [hσ]
            simp [Nat.cast_sum, Nat.cast_pow]
    _ = (((p : ℝ) ^ (k + 1) - 1) / ((p : ℝ) - 1)) / ((p : ℝ) ^ k) := by
            rw [geom_sum_eq hp1 (k + 1)]
    _ = ((p : ℝ) ^ (k + 1) - 1) / (((p : ℝ) ^ k) * ((p : ℝ) - 1)) := by
            field_simp [hp0, hp1]

/-- Euler's divisor-sum identity in quotient form:
`σ 1 n / n = ∏_{p ^ k ‖ n} (p ^ (k+1) - 1) / (p ^ k * (p - 1))`. -/
theorem sigma_ratio_prime_power_prod {n : ℕ} (hn : n ≠ 0) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ) =
      Finset.prod n.primeFactors (fun p : ℕ =>
        (((p : ℝ) ^ (n.factorization p + 1) - 1) /
          ((p : ℝ) ^ (n.factorization p) * ((p : ℝ) - 1)))) := by
  let s := n.primeFactors
  let e : ℕ → ℕ := fun p => n.factorization p
  have hfac : ArithmeticFunction.sigma 1 n =
      ∏ p ∈ s, ArithmeticFunction.sigma 1 (p ^ e p) := by
    dsimp [s, e]
    exact (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization
      (ArithmeticFunction.sigma 1) hn
  have hfacℝ : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) =
      ∏ p ∈ s, ((ArithmeticFunction.sigma 1 (p ^ e p) : ℕ) : ℝ) := by
    rw [hfac]
    simp [Nat.cast_prod]
  have hnpow : (n : ℝ) = ∏ p ∈ s, (p : ℝ) ^ e p := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    dsimp [s, e]
    simp [Nat.cast_prod, Nat.cast_pow]
  calc
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)
        = (∏ p ∈ s, ((ArithmeticFunction.sigma 1 (p ^ e p) : ℕ) : ℝ)) /
            (∏ p ∈ s, (p : ℝ) ^ e p) := by
            rw [hfacℝ, hnpow]
    _ = ∏ p ∈ s, (((ArithmeticFunction.sigma 1 (p ^ e p) : ℕ) : ℝ) / (p : ℝ) ^ e p) := by
            rw [← Finset.prod_div_distrib]
    _ = ∏ p ∈ s, (((p : ℝ) ^ (e p + 1) - 1) /
          (((p : ℝ) ^ e p) * ((p : ℝ) - 1))) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          exact sigma_one_ratio_prime_pow (p := p) (k := e p)
            (Nat.prime_of_mem_primeFactors (by simpa [s] using hp))
    _ = Finset.prod n.primeFactors (fun p : ℕ =>
          (((p : ℝ) ^ (n.factorization p + 1) - 1) /
            ((p : ℝ) ^ (n.factorization p) * ((p : ℝ) - 1)))) := by
          dsimp [s, e]

end Commons.NumberTheory.Robin
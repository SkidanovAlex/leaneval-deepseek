import Mathlib.NumberTheory.Chebyshev

open scoped ArithmeticFunction
open Finset

namespace Commons.NumberTheory.Chebyshev

-- The statement below uses an `if` over an unbounded existential
-- `∃ p e : ℕ, … n = p ^ e`, which is not computably decidable; the
-- classical instance makes the propositional `if` well-formed.
attribute [local instance] Classical.propDecidable

/-- Pointwise identity of the two indicator weights: the indicator of
`n = p ^ e` with `p` prime and `2 ≤ e` and the indicator of `¬ n.Prime`
agree once multiplied by the von Mangoldt function. -/
private lemma highPrimePowerIndic_eq (n : ℕ) :
    (if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e then ArithmeticFunction.vonMangoldt n else 0)
      = (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) := by
  classical
  by_cases hn : n.Prime
  · have hcond : ¬∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e := by
      rintro ⟨p, e, _hp, he, hpe⟩
      exact (Nat.Prime.not_prime_pow he) (hpe ▸ hn)
    rw [if_neg hcond, if_pos hn]
  · by_cases hcond : ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
    · rw [if_pos hcond, if_neg hn]
    · have hni : ¬IsPrimePow n := by
        intro hi
        rcases (isPrimePow_nat_iff n).1 hi with ⟨p, k, hp, hk0, hpk⟩
        have hk1 : k ≠ 1 := by
          intro hk1
          apply hn
          simpa [← hpk, hk1] using hp
        have hk2 : 2 ≤ k := by omega
        exact hcond ⟨p, k, hp, hk2, hpk.symm⟩
      have hzero : ArithmeticFunction.vonMangoldt n = 0 :=
        (ArithmeticFunction.vonMangoldt_eq_zero_iff).2 hni
      rw [if_neg hcond, if_neg hn, hzero]

/-- For a prime `n` the von Mangoldt value is `log n`; hence the indicator
`¬ n.Prime` extracts from `Λ n` exactly the `log n` that `θ` subtracts. -/
private lemma notPrimeIndic_eq (n : ℕ) :
    (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n)
      = ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log (n : ℝ) else 0) := by
  classical
  by_cases hn : n.Prime
  · rw [if_pos hn, if_pos hn, ArithmeticFunction.vonMangoldt_apply_prime hn, sub_self]
  · rw [if_neg hn, if_neg hn, sub_zero]

/-- The cumulative sum in question is exactly `ψ x - θ x`: it collects the
von Mangoldt values at prime powers `n = p ^ e` with `e ≥ 2`, i.e. all of
`ψ` except the contribution of the primes themselves, which is `θ`. -/
private lemma cumulative_sum_eq_psi_sub_theta (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
        then ArithmeticFunction.vonMangoldt n else 0)
      = Chebyshev.psi x - Chebyshev.theta x := by
  classical
  calc
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
        then ArithmeticFunction.vonMangoldt n else 0)
        = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) := by
          refine Finset.sum_congr rfl ?_
          intro n _
          exact highPrimePowerIndic_eq n
    _ = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
          (ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log (n : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro n _
          exact notPrimeIndic_eq n
    _ = Chebyshev.psi x - Chebyshev.theta x := by
          rw [Finset.sum_sub_distrib]
          rw [← Chebyshev.psi_eq_sum_Icc x]
          congr 1
          rw [Chebyshev.theta_eq_sum_Icc x]
          exact (Finset.sum_filter (s := Finset.Icc 0 ⌊x⌋₊) (p := fun n : ℕ => n.Prime)
            (f := fun n : ℕ => Real.log (n : ℝ))).symm

/-- The cumulative sum of the von Mangoldt function over prime powers with
exponent at least two is `O(√x)`. -/
theorem cumulativePrimePowerLeSqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
          if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
          then ArithmeticFunction.vonMangoldt n else 0) ≤ C * Real.sqrt x := by
  rcases Chebyshev.psi_sub_theta_le_mul_sqrt with ⟨C0, hC0⟩
  refine ⟨max C0 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right C0 1)
  · intro x hx
    calc
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
          if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
          then ArithmeticFunction.vonMangoldt n else 0)
          = Chebyshev.psi x - Chebyshev.theta x := cumulative_sum_eq_psi_sub_theta x
      _ ≤ C0 * Real.sqrt x := hC0 x
      _ ≤ max C0 1 * Real.sqrt x := by
          exact mul_le_mul_of_nonneg_right (le_max_left C0 1) (Real.sqrt_nonneg x)

end Commons.NumberTheory.Chebyshev
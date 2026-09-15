import Mathlib.NumberTheory.Chebyshev
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eq_sum_notPrime

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.PrimeNumberTheorem

/-- The contribution of the higher prime powers to the von Mangoldt sum is
bounded by `2√x log x` over any set of integers `≤ x`: the sum of
`Λ n − [n prime]·log n` is at most `2√x log x`. -/
theorem sum_vonMangoldt_sub_primeLog_le (x : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ≤ x) :
    (∑ n ∈ s, (ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log (n : ℝ) else 0)))
      ≤ 2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := by
  -- Pointwise: on a prime the two terms cancel, and elsewhere the prime term is `0`.
  have hterm : ∀ n : ℕ,
      ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log (n : ℝ) else 0)
        = (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n) := by
    intro n
    by_cases hn : n.Prime
    · simp [hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
    · simp [hn]
  have h0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply, if_neg not_isPrimePow_zero]
  rcases Nat.eq_zero_or_pos x with rfl | hxpos
  · -- `x = 0`: all indices are `0`, where the summand vanishes.
    have hzero : ∀ n ∈ s,
        ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log (n : ℝ) else 0) = 0 := by
      intro n hn
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero (hs n hn)
      subst hn0
      rw [h0]
      simp
    rw [Finset.sum_eq_zero hzero]
    simp
  · rw [Finset.sum_congr rfl (fun n _ => hterm n)]
    have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxpos
    -- Extend the index set to `{1, ..., x}`; the extra point `0` contributes `0`.
    have hsub : s ⊆ Finset.Icc 0 x := fun n hn =>
      Finset.mem_Icc.mpr ⟨Nat.zero_le n, hs n hn⟩
    have hle1 : (∑ n ∈ s, (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n))
        ≤ ∑ n ∈ Finset.Icc 0 x,
            (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by
        by_cases hn : n.Prime
        · simp [hn]
        · simp [hn, ArithmeticFunction.vonMangoldt_nonneg])
    have hle2 : (∑ n ∈ Finset.Icc 0 x,
            (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n))
        = ∑ n ∈ Finset.Ioc 0 x,
            (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n) := by
      symm
      apply Finset.sum_subset
      · intro n hn
        rw [Finset.mem_Ioc] at hn
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, hn.2⟩
      · intro n hnIcc hnIoc
        have hnle : n ≤ x := (Finset.mem_Icc.mp hnIcc).2
        have hn0 : n = 0 := by
          by_contra hne
          exact hnIoc (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hne, hnle⟩)
        subst hn0
        simp [Nat.not_prime_zero, h0]
    have hle3 : (∑ n ∈ Finset.Ioc 0 x,
            (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n))
        = Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime (x : ℝ), Nat.floor_natCast,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hnp : n.Prime <;> simp [hnp]
    exact hle1.trans (hle2.le.trans (hle3.le.trans (Chebyshev.psi_sub_theta_le hx1)))

end Commons.NumberTheory.PrimeNumberTheorem
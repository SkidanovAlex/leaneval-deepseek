import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open scoped BigOperators

/-- For `n ≥ 1`, the number of divisors of `n` divided by `n` can be written as a sum over the
antidiagonal of pairs `(a, b)` with `a * b = n`, each contributing `1 / (a * b) = 1 / n`. -/
lemma sum_antidiag_div_eq_card_div (n : ℕ) :
    ((n.divisors.card : ℕ) : ℝ) / (n : ℝ)
      = ∑ p ∈ n.divisorsAntidiagonal, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
  have key := Nat.sum_divisorsAntidiagonal (fun a b : ℕ => (1 : ℝ) / ((a * b : ℕ) : ℝ)) (n := n)
  rw [key]
  have h : ∑ i ∈ n.divisors, (1 : ℝ) / ((i * (n / i) : ℕ) : ℝ)
         = ∑ i ∈ n.divisors, (1 : ℝ) / (n : ℝ) :=
    Finset.sum_congr rfl (fun i hi => by
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hi)])
  rw [h, Finset.sum_const, nsmul_eq_mul, div_eq_mul_one_div]

/-- The sum over all pairs `(a, b)` in `[1, N] × [1, N]` of `1 / (a * b)` is the square of the
harmonic sum `∑_{m ≤ N} 1 / m`. -/
lemma sum_prod_recip_eq_sq (N : ℕ) :
    ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)
      = (∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ)) ^ 2 := by
  have h : ∀ x y : ℕ, (1 : ℝ) / ((x * y : ℕ) : ℝ)
      = (1 : ℝ) / (x : ℝ) * ((1 : ℝ) / (y : ℝ)) := by
    intro x y
    rw [Nat.cast_mul, ← one_div_mul_one_div]
  rw [Finset.sum_product]
  simp_rw [h]
  rw [← Finset.sum_mul_sum]
  rw [pow_two]

/-- Hyperbola bound for the sum of `d(n)/n`: it is at most the square of the `N`-th harmonic
number. -/
theorem sum_card_divisors_div_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) / (n : ℝ)
      ≤ (∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ)) ^ 2 := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [← sum_prod_recip_eq_sq N]
  calc ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) / (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
          (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro n _
        exact sum_antidiag_div_eq_card_div n
    _ = ∑ n ∈ Finset.Icc 1 N,
          ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 = n),
            (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : n ≠ 0 := by
          have : 1 ≤ n := (Finset.mem_Icc.mp hn).1; omega
        have hnle : n ≤ N := (Finset.mem_Icc.mp hn).2
        rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn0 hnle, hIoc]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
          (if p.1 * p.2 = n then (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_filter]
    _ = ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if p.1 * p.2 = n then (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
          (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        rw [Finset.sum_ite_eq]
        split_ifs with h
        · exact le_rfl
        · positivity

end Work.LinnikAreas

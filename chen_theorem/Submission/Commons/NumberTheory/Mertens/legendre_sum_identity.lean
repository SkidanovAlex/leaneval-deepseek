import Mathlib
import Submission.Commons.NumberTheory.Mertens.factorial_log_eq_sum_legendre

namespace Commons.NumberTheory.Mertens

open Finset

/-- Splitting the Legendre inner sum `∑_{1 ≤ i ≤ n} ⌊n/p^i⌋` into the `i = 1` term
plus the tail `∑_{2 ≤ i ≤ n} ⌊n/p^i⌋`. -/
lemma sum_Ico_one_split (n p : ℕ) (hp : 1 < n + 1) :
    (∑ i ∈ Finset.Ico 1 (n + 1), ((n / p ^ i : ℕ) : ℝ)) =
      ((n / p : ℕ) : ℝ) + (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) := by
  rw [← Finset.insert_Ico_succ_left_eq_Ico (a := 1) (b := n + 1) hp]
  rw [Finset.sum_insert (by simp [Finset.mem_Ico])]
  congr 1
  simp

/-- **Legendre's formula, split form.** For every `n`,
`n · Σ_{p ≤ n} (log p)/p = log(n!) − T + F`, where
`T = Σ_{p ≤ n} (Σ_{2 ≤ i ≤ n} ⌊n/p^i⌋) log p` collects the Legendre tail and
`F = Σ_{p ≤ n} (n/p − ⌊n/p⌋) log p` is the fractional-part correction.

Proof: `log(n!) = Σ_{p ≤ n} v_p(n!) log p` (`Real.log_nat_eq_sum_factorization` together with
`(n.factorial).primeFactors = n.primesLE`), `v_p(n!) = Σ_{i ≤ n} ⌊n/p^i⌋`
(`Nat.factorization_factorial`), split off `i = 1`, and note
`⌊n/p⌋ = n/p − (n/p − ⌊n/p⌋)`. -/
theorem legendre_sum_identity (n : ℕ) :
    (n : ℝ) * (∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ)) =
      Real.log (n.factorial : ℝ) -
        (∑ p ∈ n.primesLE,
          (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)) +
        (∑ p ∈ n.primesLE,
          (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)) := by
  rw [factorial_log_eq_sum_legendre n]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
  have hpn : p ≤ n := Nat.le_of_mem_primesLE hp
  have h1 : 1 < n + 1 := by have := hpp.two_le; omega
  rw [sum_Ico_one_split n p h1]
  ring

end Commons.NumberTheory.Mertens

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Totient
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_bound_of_squarefree

/-!
# `∑_{k ∣ m} φ(k)/k ≤ 2^{ω(m)}` for squarefree `m`

For squarefree `m` the number of divisors is `2^{ω(m)}`, and every summand
`φ(k)/k` is at most `1` (because `φ(k) ≤ k`).  Hence the sum is bounded by the
number of divisors.

The divisor count of a squarefree number is provided by the commons lemma
`Commons.NumberTheory.FriedlanderIwaniec.card_divisors_of_squarefree`.
-/

namespace Commons.NumberTheory.ArithmeticFunction

open Finset

theorem sum_totient_div_divisors_le_two_pow_omega {m : ℕ} (hm : Squarefree m) :
    ∑ k ∈ m.divisors, (Nat.totient k : ℝ) / (k : ℝ) ≤ 2 ^ (m.primeFactors).card := by
  have hcard : m.divisors.card = 2 ^ (m.primeFactors).card :=
    _root_.Commons.NumberTheory.FriedlanderIwaniec.card_divisors_of_squarefree hm.ne_zero hm
  calc ∑ k ∈ m.divisors, (Nat.totient k : ℝ) / (k : ℝ)
      ≤ ∑ _k ∈ m.divisors, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hkdvd : k ∣ m := Nat.dvd_of_mem_divisors hk
        have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hkdvd (Nat.pos_of_ne_zero hm.ne_zero)
        have hkpos' : 0 < (k : ℝ) := by exact_mod_cast hkpos
        exact (div_le_one hkpos').mpr (by exact_mod_cast Nat.totient_le k)
    _ = m.divisors.card := by simp
    _ = 2 ^ (m.primeFactors).card := by simp [hcard]

end Commons.NumberTheory.ArithmeticFunction
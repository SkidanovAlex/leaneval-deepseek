import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Commons.NumberTheory.Nat.radical_eq_prod_primeFactors

namespace Commons.NumberTheory.Nat

/-- If `C` equals the product of its distinct prime factors (i.e. `C` is squarefree),
then the number of divisors of `C` is `2` to the number of distinct prime factors of `C`.
Hence in particular `C.divisors.card ≤ 2 ^ C.primeFactors.card`. -/
theorem card_divisors_le_two_pow_card_primeFactors (C : ℕ)
    (hC : C = ∏ p ∈ C.primeFactors, p) :
    C.divisors.card ≤ 2 ^ C.primeFactors.card := by
  have hsf : Squarefree C := by
    have h : Squarefree (radical C) := radical_squarefree C
    rwa [show radical C = C from hC.symm] at h
  have hne : C ≠ 0 := hsf.ne_zero
  have hcard : C.divisors.card = 2 ^ C.primeFactors.card := by
    rw [Nat.card_divisors hne]
    have hcongr : C.primeFactors.prod (fun p => C.factorization p + 1)
        = C.primeFactors.prod (fun _ => 2) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hp' := Nat.mem_primeFactors.mp hp
      have hge : 1 ≤ C.factorization p := hp'.1.factorization_pos_of_dvd hne hp'.2.1
      have hle : C.factorization p ≤ 1 := hsf.natFactorization_le_one p
      omega
    rw [hcongr, Finset.prod_const]
  exact le_of_eq hcard

end Commons.NumberTheory.Nat
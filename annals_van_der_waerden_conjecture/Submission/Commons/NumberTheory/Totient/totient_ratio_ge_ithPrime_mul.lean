import Mathlib
import Submission.Commons.NumberTheory.Nat.prod_one_sub_inv_ge_ithPrime
import Submission.Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv

namespace Commons.NumberTheory.Totient

open Finset

theorem totient_ratio_ge_ithPrime_mul (n p : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0) (hpn : ¬ p ∣ n) :
    (∏ i ∈ Finset.range ((n.primeFactors).card + 1), (1 - (1 : ℚ) / ((Nat.nth Nat.Prime i : ℕ) : ℚ)))
        * ((p : ℚ) / ((p : ℚ) - 1))
      ≤ (Nat.totient n : ℚ) / (n : ℚ) := by
  classical
  set S : Finset ℕ := insert p n.primeFactors with hSdef
  have hp_notin : p ∉ n.primeFactors := by
    intro h
    exact hpn (Nat.mem_primeFactors.mp h).2.1
  have hScard : S.card = (n.primeFactors).card + 1 := by
    rw [hSdef, Finset.card_insert_of_notMem hp_notin]
  have hSprimes : ∀ x ∈ S, Nat.Prime x := by
    intro x hx
    rw [hSdef, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hp
    · exact Nat.prime_of_mem_primeFactors hx
  -- combinatorial bound: the product over the first `S.card` primes is at most over `S`
  have hcomb := Commons.NumberTheory.Nat.prod_one_sub_inv_ge_ithPrime S hSprimes
  rw [hScard] at hcomb
  have hprodS : ∏ x ∈ S, (1 - (1 : ℚ) / (x : ℚ))
      = (1 - (1 : ℚ) / (p : ℚ))
          * ∏ x ∈ n.primeFactors, (1 - (1 : ℚ) / (x : ℚ)) := by
    rw [hSdef, Finset.prod_insert hp_notin]
  have hA : (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
        (1 - (1 : ℚ) / ((Nat.nth Nat.Prime i : ℕ) : ℚ)))
      ≤ (1 - (1 : ℚ) / (p : ℚ))
          * ∏ x ∈ n.primeFactors, (1 - (1 : ℚ) / (x : ℚ)) := by
    rw [← hprodS]
    exact hcomb
  -- `(1 - 1/p) * (p/(p-1)) = 1`
  have hgp : (1 - (1 : ℚ) / (p : ℚ)) * ((p : ℚ) / ((p : ℚ) - 1)) = 1 := by
    have hp2 : 1 < p := hp.one_lt
    have hpc : (p : ℚ) ≠ 0 := by
      have : p ≠ 0 := by omega
      exact_mod_cast this
    have hp1 : (p : ℚ) - 1 ≠ 0 := by
      have : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp2
      linarith
    field_simp
  have hc_nonneg : (0 : ℚ) ≤ (p : ℚ) / ((p : ℚ) - 1) := by
    apply div_nonneg
    · exact_mod_cast (Nat.zero_le p)
    · have : (1 : ℚ) ≤ (p : ℚ) := by
        have : 1 ≤ p := hp.one_le
        exact_mod_cast this
      linarith
  have heuler := Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv n hn
  calc (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
          (1 - (1 : ℚ) / ((Nat.nth Nat.Prime i : ℕ) : ℚ)))
        * ((p : ℚ) / ((p : ℚ) - 1))
      ≤ ((1 - (1 : ℚ) / (p : ℚ))
          * ∏ x ∈ n.primeFactors, (1 - (1 : ℚ) / (x : ℚ)))
          * ((p : ℚ) / ((p : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_right hA hc_nonneg
    _ = (∏ x ∈ n.primeFactors, (1 - (1 : ℚ) / (x : ℚ)))
          * ((1 - (1 : ℚ) / (p : ℚ)) * ((p : ℚ) / ((p : ℚ) - 1))) := by ring
    _ = (∏ x ∈ n.primeFactors, (1 - (1 : ℚ) / (x : ℚ))) := by rw [hgp, mul_one]
    _ = (Nat.totient n : ℚ) / (n : ℚ) := heuler.symm

end Commons.NumberTheory.Totient

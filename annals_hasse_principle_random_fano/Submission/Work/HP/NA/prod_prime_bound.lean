import Mathlib
import Submission.Work.HP.Defs

/-!
# Euler-product type bound: `∏_{p ≤ w} (1 + C / p^{5/4}) ≤ exp (5 C)`

For every `C > 0` and real `w`, the product of `1 + C / p^{5/4}` over the primes
`p ≤ w` is at most `exp (5 * C)`.

The proof has two ingredients:
* `1 + x ≤ exp x`, so the product is at most `exp (C * ∑_{p ≤ w} p^{-5/4})`;
* the reciprocal-power sum over the primes is at most `5`: it is dominated by the
  integral `∫_{x > 1} x^{-5/4} = 4` (integral test for the antitone function
  `x ↦ x^{-5/4}`), via `AntitoneOn.sum_Ico_le_integral`.
-/

namespace Work.HP.NA

open Finset

/-- The sum of `p^{-5/4}` over the primes `p ≤ N` is at most `5`.

It is bounded by the tail of the integral test: primes are `≥ 2`, so the sum is
dominated by `∑_{2 ≤ n ≤ N+1} n^{-5/4} ≤ ∫_{x > 1} x^{-5/4} = 4 ≤ 5`. -/
theorem sum_primesLE_rpow_le (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (p:ℝ)^(-((5:ℝ)/4)) ≤ 5 := by
  have hsub : Nat.primesLE N ⊆ Finset.Ico 2 (N+2) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    simp only [Finset.mem_Ico]
    exact ⟨hp.2.two_le, by omega⟩
  have hsum : ∑ p ∈ Finset.Ico 2 (N+2), (p:ℝ)^(-((5:ℝ)/4))
      = ∑ n ∈ Finset.Ico 1 (N+1), ((n+1:ℕ):ℝ)^(-((5:ℝ)/4)) := by
    rw [← Finset.sum_Ico_add (fun x : ℕ => (x:ℝ)^(-((5:ℝ)/4))) 1 (N+1) 1]
    apply Finset.sum_congr rfl
    intro n _
    simp [Nat.add_comm]
  calc ∑ p ∈ Nat.primesLE N, (p:ℝ)^(-((5:ℝ)/4))
      ≤ ∑ p ∈ Finset.Ico 2 (N+2), (p:ℝ)^(-((5:ℝ)/4)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i hi _
        exact Real.rpow_nonneg (by positivity) _
    _ = ∑ n ∈ Finset.Ico 1 (N+1), ((n+1:ℕ):ℝ)^(-((5:ℝ)/4)) := hsum
    _ ≤ ∫ x in Set.Ioi (1:ℝ), x ^ (-((5:ℝ)/4)) := by
        have h := AntitoneOn.sum_Ico_le_integral
          (f := fun x : ℝ => x ^ (-((5:ℝ)/4))) (a := 1) (b := N+1)
          ((Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
            (by intro x hx; rw [Set.mem_Icc] at hx; rw [Set.mem_Ioi]
                simp only [Nat.cast_one] at hx; linarith [hx.1]))
          (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num))
          (by intro t ht; rw [Set.mem_Ioi] at ht; simp only [Nat.cast_one] at ht
              exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _)
        simpa using h
    _ ≤ 5 := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
        norm_num [Real.one_rpow]

theorem prod_prime_bound (C : ℝ) (hC : 0 < C) (w : ℝ) :
    ∏ p ∈ (Finset.range (⌊w⌋₊+1)).filter Nat.Prime, (1 + C / (p:ℝ)^((5:ℝ)/4))
      ≤ Real.exp (5 * C) := by
  rw [← Nat.primesLE_eq_filter_range]
  have hprod : ∏ p ∈ Nat.primesLE ⌊w⌋₊, (1 + C / (p:ℝ)^((5:ℝ)/4))
      ≤ Real.exp (∑ p ∈ Nat.primesLE ⌊w⌋₊, C / (p:ℝ)^((5:ℝ)/4)) := by
    calc ∏ p ∈ Nat.primesLE ⌊w⌋₊, (1 + C / (p:ℝ)^((5:ℝ)/4))
        ≤ ∏ p ∈ Nat.primesLE ⌊w⌋₊, Real.exp (C / (p:ℝ)^((5:ℝ)/4)) := by
          apply Finset.prod_le_prod₀
          · intro p hp; positivity
          · intro p hp
            simpa [add_comm] using Real.add_one_le_exp (C / (p:ℝ)^((5:ℝ)/4))
      _ = Real.exp (∑ p ∈ Nat.primesLE ⌊w⌋₊, C / (p:ℝ)^((5:ℝ)/4)) :=
          (Real.exp_sum _ _).symm
  refine le_trans hprod ?_
  apply Real.exp_le_exp.mpr
  have hsumC : ∑ p ∈ Nat.primesLE ⌊w⌋₊, C / (p:ℝ)^((5:ℝ)/4)
      = C * ∑ p ∈ Nat.primesLE ⌊w⌋₊, (p:ℝ)^(-((5:ℝ)/4)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.rpow_neg (Nat.cast_nonneg p), div_eq_mul_inv]
  rw [hsumC]
  calc C * ∑ p ∈ Nat.primesLE ⌊w⌋₊, (p:ℝ)^(-((5:ℝ)/4))
      ≤ C * 5 := mul_le_mul_of_nonneg_left (sum_primesLE_rpow_le ⌊w⌋₊) (le_of_lt hC)
    _ = 5 * C := by ring

end Work.HP.NA

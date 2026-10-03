import Mathlib
import Submission.Commons.NumberTheory.Nat.omega_color_sum_weighted_le
import Submission.Commons.NumberTheory.ArithmeticFunction.card_Omega_eq_le

/-!
# `∑_{n ≤ N} 2^{ω(n)} / n ≤ (1 + log N)^2`

The power-weighted `ω`-colouring bound (`Commons.NumberTheory.Nat.omega_color_sum_weighted_le`)
with `c = 2` and `s = 1` already gives

`∑_{n ≤ N} 2^{ω(n)} · n^{-1} ≤ (∑_{k ≤ N} k^{-1})²`,

and the harmonic sum `∑_{k ≤ N} 1/k ≤ 1 + log N`
(`Commons.NumberTheory.ArithmeticFunction.sum_inv_Icc_one_le_one_add_log`)
finishes the estimate.
-/

namespace Commons.NumberTheory.ArithmeticFunction

open Finset

theorem sum_two_pow_omega_div_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (2 : ℝ) ^ (Nat.primeFactors n).card / (n : ℝ)) ≤
      (1 + Real.log N) ^ 2 := by
  have hmain := _root_.Commons.NumberTheory.Nat.omega_color_sum_weighted_le 2 N
    (by norm_num) 1 (by norm_num)
  have hL : (∑ n ∈ Finset.Icc 1 N, (2 : ℝ) ^ (Nat.primeFactors n).card / (n : ℝ))
      = ∑ a ∈ Finset.Icc 1 N, (2 : ℝ) ^ (a.primeFactors).card * Real.rpow (a : ℝ) (-1) := by
    apply Finset.sum_congr rfl
    intro n _
    have hrpow : Real.rpow (n : ℝ) (-1) = (n : ℝ)⁻¹ := Real.rpow_neg_one n
    rw [hrpow, div_eq_mul_inv]
  rw [hL]
  refine le_trans hmain ?_
  have hS : (∑ k ∈ Finset.Icc 1 N, Real.rpow (k : ℝ) (-1))
      = ∑ i ∈ Finset.Icc 1 N, (1 : ℝ) / (i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    have hrpow : Real.rpow (i : ℝ) (-1) = (i : ℝ)⁻¹ := Real.rpow_neg_one i
    rw [hrpow, one_div]
  rw [hS]
  exact pow_le_pow_left₀
    (Finset.sum_nonneg (fun i _ => by
      rw [one_div]
      exact inv_nonneg.mpr (by positivity)))
    (sum_inv_Icc_one_le_one_add_log N) 2

end Commons.NumberTheory.ArithmeticFunction

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Commons.Analysis.Summation.sum_choose_neg_one_pow_div_add

noncomputable section
open MeasureTheory
open scoped Interval BigOperators

namespace Commons.Analysis.Integral

open Finset

private lemma int_expand (q n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ q * (1 - x ^ 3) ^ n)
      = ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * (-1 : ℝ) ^ j / ((q : ℝ) + 1 + 3 * (j : ℝ)) := by
  have hpoly : ∀ x : ℝ, (1 - x ^ 3) ^ n
      = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (-1 : ℝ) ^ j * x ^ (3 * j) := by
    intro x
    rw [show (1 - x ^ 3 : ℝ) = (-(x ^ 3)) + 1 by ring, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    rw [one_pow, mul_one, show (-(x ^ 3) : ℝ) = (-1) * x ^ 3 by ring, mul_pow, ← pow_mul]
    ring
  have hcongr : (∫ x in (0 : ℝ)..1, x ^ q * (1 - x ^ 3) ^ n)
      = ∫ x in (0 : ℝ)..1,
          ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℝ) * (-1 : ℝ) ^ j * x ^ (q + 3 * j) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only
    rw [hpoly x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hpow : x ^ q * x ^ (3 * j) = x ^ (q + 3 * j) := by rw [← pow_add]
    calc x ^ q * ((n.choose j : ℝ) * (-1 : ℝ) ^ j * x ^ (3 * j))
        = (x ^ q * x ^ (3 * j)) * ((n.choose j : ℝ) * (-1 : ℝ) ^ j) := by ring
      _ = x ^ (q + 3 * j) * ((n.choose j : ℝ) * (-1 : ℝ) ^ j) := by rw [hpow]
      _ = (n.choose j : ℝ) * (-1 : ℝ) ^ j * x ^ (q + 3 * j) := by ring
  rw [hcongr]
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro j hj
    exact (Continuous.intervalIntegrable (by continuity) 0 1)
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp
  ring

lemma int_pow_mul_one_sub_cube_general (q n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ q * (1 - x ^ 3) ^ n) =
      ((3 : ℝ) ^ n * (n.factorial : ℝ))
        / ∏ k ∈ Finset.range (n + 1), ((q : ℝ) + 1 + 3 * (k : ℝ)) := by
  rw [int_expand]
  set X : ℝ := ((q : ℝ) + 1) / 3 with hX
  have hx : ∀ i : ℕ, i ≤ n → X + (i : ℝ) ≠ 0 := by
    intro i hi
    have : 0 < X + (i : ℝ) := by rw [hX]; positivity
    positivity
  have hsum := Commons.Analysis.Summation.sum_choose_neg_one_pow_div_add X n hx
  have hterm : ∀ j : ℕ, (n.choose j : ℝ) * (-1 : ℝ) ^ j / ((q : ℝ) + 1 + 3 * (j : ℝ))
      = (1 / 3) * ((-1 : ℝ) ^ j * (n.choose j : ℝ) / (X + (j : ℝ))) := by
    intro j
    have hXj : X + (j : ℝ) = ((q : ℝ) + 1 + 3 * (j : ℝ)) / 3 := by rw [hX]; ring
    rw [hXj]
    have hD : ((q : ℝ) + 1 + 3 * (j : ℝ)) ≠ 0 := by positivity
    field_simp
  have hL : (∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * (-1 : ℝ) ^ j / ((q : ℝ) + 1 + 3 * (j : ℝ)))
      = (1 / 3) * ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℝ) ^ j * (n.choose j : ℝ) / (X + (j : ℝ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj => hterm j)
  have hprod : ∏ k ∈ Finset.range (n + 1), (X + (k : ℝ))
      = (∏ k ∈ Finset.range (n + 1), ((q : ℝ) + 1 + 3 * (k : ℝ))) / 3 ^ (n + 1) := by
    have hfac : ∀ k : ℕ, X + (k : ℝ) = ((q : ℝ) + 1 + 3 * (k : ℝ)) / 3 := by
      intro k; rw [hX]; ring
    rw [Finset.prod_congr rfl (fun k hk => hfac k), Finset.prod_div_distrib]
    congr 1
    rw [Finset.prod_const, Finset.card_range]
  rw [hL, hsum, hprod]
  have hP : (∏ k ∈ Finset.range (n + 1), ((q : ℝ) + 1 + 3 * (k : ℝ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    positivity
  field_simp
  rw [pow_succ]
  ring

end Commons.Analysis.Integral
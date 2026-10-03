/-
# `Work.FIChain.FIgtil_prime_sum_loglog`

The partial sum of the modified density `g̃ = Submission.ASP.FIgtil` over the primes `p ≤ y`
satisfies

  `∑_{p ≤ y} g̃(p) ≤ log log y + K`   for all real `y ≥ 2`,

with a constant `K` independent of `y`.  This is the `O(1)` form of the companion's (1.9)

  `∑_{p ≤ y} g̃(p) = log log y + c + O((log y)^{-10} + 1/y)`,

whose `ℕ`-indexed version is `Submission.ASP.FIgtil_sum_19_nat`: since the error term is
uniformly bounded by `(log 2)^{-10} + 1/2` for `y ≥ 2`, the constant
`K = c + |C|·((log 2)^{-10} + 1/2)` works.
-/
import Mathlib
import Submission.ASP.S27

namespace Work.FIChain

open Finset

noncomputable section

theorem FIgtil_prime_sum_loglog :
    ∃ K : ℝ, ∀ y : ℕ, 2 ≤ y →
      (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, Submission.ASP.FIgtil p)
        ≤ Real.log (Real.log (y : ℝ)) + K := by
  obtain ⟨c, C, h19⟩ := Submission.ASP.FIgtil_sum_19_nat
  refine ⟨c + |C| * ((Real.log 2) ^ (-(10 : ℝ)) + 1 / 2), ?_⟩
  intro y hy
  have hy1 : (1 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 1 < y)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ Real.log (y : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hy)
  have hX0 : 0 ≤ (Real.log (y : ℝ)) ^ (-(10 : ℝ)) + 1 / (y : ℝ) := by
    have h1 : 0 < (Real.log (y : ℝ)) ^ (-(10 : ℝ)) := Real.rpow_pos_of_pos hlogy _
    have h2 : 0 < 1 / (y : ℝ) := by
      apply one_div_pos.mpr
      exact_mod_cast (by omega : 0 < y)
    linarith
  have hXle : (Real.log (y : ℝ)) ^ (-(10 : ℝ)) + 1 / (y : ℝ)
      ≤ (Real.log 2) ^ (-(10 : ℝ)) + 1 / 2 := by
    have h1 : (Real.log (y : ℝ)) ^ (-(10 : ℝ)) ≤ (Real.log 2) ^ (-(10 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hlog2 hlogle (by norm_num)
    have h2 : 1 / (y : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hy)
    linarith
  have habs : (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, Submission.ASP.FIgtil p)
      - Real.log (Real.log (y : ℝ)) - c
      ≤ |C| * ((Real.log 2) ^ (-(10 : ℝ)) + 1 / 2) := by
    calc (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, Submission.ASP.FIgtil p)
          - Real.log (Real.log (y : ℝ)) - c
        ≤ C * ((Real.log (y : ℝ)) ^ (-(10 : ℝ)) + 1 / (y : ℝ)) := (abs_le.mp (h19 y hy)).2
      _ ≤ |C| * ((Real.log (y : ℝ)) ^ (-(10 : ℝ)) + 1 / (y : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hX0
      _ ≤ |C| * ((Real.log 2) ^ (-(10 : ℝ)) + 1 / 2) :=
          mul_le_mul_of_nonneg_left hXle (abs_nonneg C)
  linarith

end

end Work.FIChain

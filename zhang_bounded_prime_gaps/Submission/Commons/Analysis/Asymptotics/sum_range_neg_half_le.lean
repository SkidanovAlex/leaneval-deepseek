import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le

open scoped Real BigOperators
set_option autoImplicit false

namespace Commons.Analysis.Asymptotics

/-- Pointwise step bound: for `n ≥ 1`, `(√n)⁻¹ ≤ 3·(√(n+1) − √n)`. -/
lemma sqrt_inv_le_three_sqrt_sub (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt (n : ℝ))⁻¹ ≤ 3 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
  let s : ℝ := Real.sqrt (n : ℝ)
  let t : ℝ := Real.sqrt ((n : ℝ) + 1)
  change s⁻¹ ≤ 3 * (t - s)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hns : s ^ 2 = (n : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
  have hnt : t ^ 2 = (n : ℝ) + 1 := by
    dsimp [t]
    exact Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hs_pos : 0 < s := by
    dsimp [s]
    rw [Real.sqrt_pos]
    positivity
  have ht_pos : 0 < t := by
    dsimp [t]
    rw [Real.sqrt_pos]
    positivity
  have hsum_pos : 0 < t + s := by linarith [hs_pos, ht_pos]
  have hts : 0 < t - s := by
    have hprod : (t - s) * (t + s) = 1 := by nlinarith
    have hsum_ne : t + s ≠ 0 := ne_of_gt hsum_pos
    have hts_eq : t - s = (t + s)⁻¹ := by
      field_simp [hsum_ne]
      nlinarith
    rw [hts_eq]
    positivity
  have hts_le : t ≤ 2 * s := by
    dsimp [t, s]
    have hsq : (2 * Real.sqrt (n : ℝ)) ^ 2 = 4 * (n : ℝ) := by
      rw [pow_two]
      nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        ((n : ℝ) + 1) ≤ 4 * (n : ℝ) := by nlinarith
        _ = (2 * Real.sqrt (n : ℝ)) ^ 2 := by rw [← hsq]
  have hone : 1 = (t - s) * (t + s) := by nlinarith
  have hle : 1 ≤ 3 * s * (t - s) := by
    calc
      1 = (t - s) * (t + s) := hone
      _ ≤ (t - s) * (3 * s) := by
        have hsum : t + s ≤ 3 * s := by linarith
        exact mul_le_mul_of_nonneg_left hsum (le_of_lt hts)
      _ = 3 * s * (t - s) := by ring
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hdiv : (1 : ℝ) / s ≤ 3 * (t - s) := by
    rw [div_le_iff₀ hs_pos]
    nlinarith [hle]
  simpa using hdiv

/-- For `n ≥ 1`, `n^(-1/2) = (√n)⁻¹`. -/
lemma rpow_neg_half_eq_inv_sqrt (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
  rw [Real.rpow_neg (show 0 ≤ (n : ℝ) by positivity)]
  rw [← Real.sqrt_eq_rpow]

/-- Pointwise bound `n^(-1/2) ≤ 3·(√(n+1) − √n)` valid for every `n : ℕ`. -/
lemma summand_le_sqrt_sub (n : ℕ) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    have h0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
    rw [h0, Real.zero_rpow]
    · norm_num
    · norm_num
  · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    rw [rpow_neg_half_eq_inv_sqrt n hn1]
    simpa using sqrt_inv_le_three_sqrt_sub n hn1

/-- Telescoping sum of square-root steps: `∑_{n < X} (√(n+1) − √n) = √X`. -/
lemma sum_range_sqrt_sub (X : ℕ) :
    (∑ n ∈ Finset.range X, (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ))) =
      Real.sqrt (X : ℝ) := by
  have h := Finset.sum_range_sub (f := fun i : ℕ => Real.sqrt (i : ℝ)) X
  simpa [Real.sqrt_zero] using h

/-- Partial sums of `n^(-1/2)` grow at most like `3·√X`: for `X ≥ 1`,
`∑_{n < X} n^(-1/2) ≤ 3·√X`. -/
theorem sum_range_neg_half_le {X : ℕ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.range X, (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 3 * Real.sqrt (X : ℝ) := by
  have _hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  calc
    (∑ n ∈ Finset.range X, (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        ∑ n ∈ Finset.range X, 3 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
      exact Finset.sum_le_sum (fun n _hn => summand_le_sqrt_sub n)
    _ = 3 * Real.sqrt (X : ℝ) := by
      rw [← Finset.mul_sum]
      rw [sum_range_sqrt_sub]

end Commons.Analysis.Asymptotics
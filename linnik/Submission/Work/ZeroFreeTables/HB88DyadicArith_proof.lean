import Mathlib

/-!
# Heath–Brown (1992), dyadic arithmetic for Lemma 8.8

We prove the elementary numeric inequality

  `exp (-L) < 2^{-(j+1)} · λ² · exp (-((11/12 + 8ε + 2^{-j}) λ))`

under the hypotheses `2^j ≤ λ < 2^{j+1}`, `λ ≥ 15.344`, `0 < ε' ≤ 1/100`,
`8ε ≤ ε'/2` and `L ≥ λ/(12/11 - ε')`.

## The mathematics

Write `s = 2^j`, `λ = lam2`, `c = 11/12 + 8ε`, `D = 12/11 - ε'` and
`t = λ/s ∈ [1,2)`.  Since `L ≥ λ/D` we have `exp (-L) ≤ exp (-λ/D)`, and

  `exp (-λ/D) = exp (-(c + 1/s)λ) · exp (t - βλ)`  with `β = 1/D - c > 0`.

Because `β > 0`, the second factor is `< exp t < exp 2`, while the prefactor
`λ²/(2 s) = (λ/2)·t ≥ λ/2 ≥ 15.344/2 > exp 2`.  So the exponential factor
`exp (t - βλ)` is dominated by the polynomial prefactor and the inequality is
strict.

The only non-trivial input is `β > 0`, i.e. `1/(12/11 - ε') > 11/12 + 8ε`,
which follows from `8ε ≤ ε'/2` and
`1/(12/11 - ε') - 11/12 = 11ε'/(12(12/11 - ε')) ≥ 11ε'/12/(12/11) > ε'/2`.
-/

namespace Work.ZeroFreeTables

set_option linter.unusedVariables false in
theorem HB88DyadicArith_proof (εe ε' L lam2 : ℝ) (j : ℕ)
    (hεe0 : 0 < εe) (hεe1 : 8 * εe ≤ ε' / 2) (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 100)
    (hL : 0 < L) (hLc : lam2 / (12 / 11 - ε') ≤ L)
    (hj1 : (2 : ℝ) ^ j ≤ lam2) (hj2 : lam2 < (2 : ℝ) ^ (j + 1))
    (hbig : 15344 / 1000 ≤ lam2) :
    Real.exp (-L) < 1 / (2 : ℝ) ^ (j + 1) * lam2 ^ 2 *
      Real.exp (-((11 / 12 + 8 * εe + 1 / (2 : ℝ) ^ j) * lam2)) := by
  -- Notation: s = 2^j, D = 12/11 - ε', and β = 1/D - (11/12 + 8ε).
  set s : ℝ := (2 : ℝ) ^ j with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have h2s : (2 : ℝ) ^ (j + 1) = 2 * s := by rw [pow_succ, ← hs_def]; ring
  have hs_le : s ≤ lam2 := hj1
  have h_lt : lam2 < 2 * s := by rw [← h2s]; exact hj2
  have hlam_pos : 0 < lam2 := lt_of_lt_of_le (by norm_num) hbig
  have hbig' : (15344 : ℝ) / 1000 ≤ lam2 := hbig
  -- `1/(12/11 - ε')` exceeds `11/12 + 8ε`.
  have hD_pos : 0 < 12 / 11 - ε' := by
    have h : (0 : ℝ) < 12 / 11 - 1 / 100 := by norm_num
    linarith
  have hβ : 11 / 12 + 8 * εe < 1 / (12 / 11 - ε') := by
    rw [lt_div_iff₀ hD_pos]
    have key : (11 / 12 + ε' / 2) * (12 / 11 - ε') < 1 := by nlinarith [hε'0]
    have hmul : (11 / 12 + 8 * εe) * (12 / 11 - ε') ≤ (11 / 12 + ε' / 2) * (12 / 11 - ε') :=
      mul_le_mul_of_nonneg_right (by linarith) hD_pos.le
    linarith
  have hβpos : 0 < 1 / (12 / 11 - ε') - (11 / 12 + 8 * εe) := by linarith
  -- `exp 2 < 15344/2000 ≤ lam2/2`.
  have hexp2 : Real.exp 2 < 15344 / 2000 := by
    have hsq : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; ring
    rw [hsq]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hnum : Real.exp 2 < lam2 / 2 := by linarith [hexp2, hbig']
  -- `t = lam2/s ∈ [1,2)`.
  have ht_ge : 1 ≤ lam2 / s := by
    rw [le_div_iff₀ hs_pos]; linarith [hs_le]
  have ht_lt : lam2 / s < 2 := by
    rw [div_lt_iff₀ hs_pos]; linarith [h_lt]
  -- The exponential factor is smaller than the polynomial prefactor.
  have hArg : lam2 / s - (1 / (12 / 11 - ε') - (11 / 12 + 8 * εe)) * lam2 < 2 := by
    have h1 : 0 < (1 / (12 / 11 - ε') - (11 / 12 + 8 * εe)) * lam2 := mul_pos hβpos hlam_pos
    linarith [ht_lt, h1]
  have hA : Real.exp (lam2 / s - (1 / (12 / 11 - ε') - (11 / 12 + 8 * εe)) * lam2) < lam2 / 2 := by
    have h1 : Real.exp (lam2 / s - (1 / (12 / 11 - ε') - (11 / 12 + 8 * εe)) * lam2) < Real.exp 2 :=
      Real.exp_lt_exp.mpr hArg
    linarith [h1, hnum]
  have hA2 : Real.exp (lam2 / s - (1 / (12 / 11 - ε') - (11 / 12 + 8 * εe)) * lam2) <
      (lam2 / 2) * (lam2 / s) := by
    have h1 : lam2 / 2 ≤ (lam2 / 2) * (lam2 / s) := by
      have h2 := mul_le_mul_of_nonneg_left ht_ge (by linarith : (0 : ℝ) ≤ lam2 / 2)
      simpa using h2
    linarith [hA, h1]
  have hmain : Real.exp (lam2 / s - (1 / (12 / 11 - ε') - (11 / 12 + 8 * εe)) * lam2) <
      lam2 ^ 2 / (2 * s) := by
    have h2 : lam2 ^ 2 / (2 * s) = (lam2 / 2) * (lam2 / s) := by
      field_simp [hs_pos.ne']
    rw [h2]; exact hA2
  -- Assemble: `exp (-λ/D) = exp (-(c+1/s)λ) · exp (t - βλ)`.
  have hexp_eq : Real.exp (-(lam2 / (12 / 11 - ε'))) =
      Real.exp (-((11 / 12 + 8 * εe + 1 / s) * lam2)) *
      Real.exp (lam2 / s - (1 / (12 / 11 - ε') - (11 / 12 + 8 * εe)) * lam2) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hs_pos.ne', hD_pos.ne']
    ring
  have hstep2 : Real.exp (-(lam2 / (12 / 11 - ε'))) <
      1 / (2 : ℝ) ^ (j + 1) * lam2 ^ 2 * Real.exp (-((11 / 12 + 8 * εe + 1 / s) * lam2)) := by
    have h1 : Real.exp (-(lam2 / (12 / 11 - ε'))) <
        Real.exp (-((11 / 12 + 8 * εe + 1 / s) * lam2)) * (lam2 ^ 2 / (2 * s)) := by
      rw [hexp_eq]
      exact mul_lt_mul_of_pos_left hmain (Real.exp_pos _)
    have h2 : Real.exp (-((11 / 12 + 8 * εe + 1 / s) * lam2)) * (lam2 ^ 2 / (2 * s)) =
        1 / (2 : ℝ) ^ (j + 1) * lam2 ^ 2 * Real.exp (-((11 / 12 + 8 * εe + 1 / s) * lam2)) := by
      rw [h2s]
      field_simp [hs_pos.ne']
    rw [h2] at h1
    exact h1
  -- `L ≥ lam2/D` finishes.
  have hstep1 : Real.exp (-L) ≤ Real.exp (-(lam2 / (12 / 11 - ε'))) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith [hstep1, hstep2]

end Work.ZeroFreeTables

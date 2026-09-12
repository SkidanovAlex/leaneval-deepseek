import Submission.PotentialDefs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt

/-!
# Serre's constant is negative (contract A3-num)

With `a = 0.087353`, `b = 4.411076`, `gamma = 0.215485`,

    serreConstant = -log((b-a)/4) + gamma*log((a + 2*sqrt(a*b) + b)/4)   ~ -1.29e-7 < 0

The value is transcendental, so the proof is by rigorous rational bounds on
the logarithms at the (irrational) arguments.  Concrete route (numbers
verified to 40 digits):

1. `serreConstant < 0` iff `gamma*log X < log Y` with
   `X := (a + 2*sqrt(a*b) + b)/4`, `Y := (b-a)/4 = 1.08093075` (exact rational).
   Numerically: sqrt(a*b) ~ 0.620742073512, X ~ 1.434978286756,
   log X ~ 0.361149718, log Y ~ 0.07782247555,
   C = -logY + gamma*logX ~ -1.28585e-7 < 0 (margin to zero ~1.3e-7).
2. Bracket the square root by rationals whose squares bracket a*b:
   0.62074206^2 < a*b < 0.62074208^2 (both verified).  With s2 := 0.62074208,
   set x2 := (a + 2*s2 + b)/4 (an exact rational ~ 1.43497829), so X < x2
   (monotonicity of sqrt and of the affine map).
3. Rational bounds on log at the rationals x2 > 1 and Y > 1: via the
   convergent series log(1+w) = 2·∑_{k≥0} y^(2k+1)/(2k+1) with
   y = w/(w+2) (the artanh substitution; mathlib `Real.sum_range_le_log_div`
   and `Real.log_div_le_sum_range_add`), partial sums give lower bounds and
   partial sums plus the explicit tail bound give upper bounds.  Use the
   UPPER bound at u = x2 - 1 with 6 terms (tail < ~4e-10) and the LOWER
   bound at v = Y - 1 with 4 terms (tail < ~5e-14).  Then
   gamma*(upper at u) < (lower at v) with a ~1.28e-7 gap, checked exactly
   by `norm_num` on rationals.
4. Chain: gamma*log X ≤ gamma*log x2 ≤ gamma*S+(u) < S-(v) ≤ log Y,
   giving gamma*log X < log Y, i.e. serreConstant < 0.  Justify the steps
   with Real.log monotonicity, Real.sqrt monotonicity (`Real.sqrt_lt` /
   `sq_lt_sq`), and the series bounds (private lemmas below).
-/

noncomputable section

open scoped Real BigOperators

namespace Submission.SerreConstantNeg

open Submission.PotentialDefs
open Submission.SerreExample

/-- Upper bound for `log(1+x)`: the first `n` odd terms of the series
`log(1+x) = 2·∑_{k≥0} (x/(x+2))^(2k+1)/(2k+1)` plus the explicit tail bound of
`Real.log_div_le_sum_range_add`.  Valid for `0 ≤ x`. -/
private lemma log_one_add_le_atanh {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.log (1 + x) ≤
      2 * ((∑ i ∈ Finset.range n,
            (x / (x + 2)) ^ (2 * i + 1) / ((2 : ℝ) * i + 1)) +
          (x / (x + 2)) ^ (2 * n + 1) / (1 - (x / (x + 2)) ^ 2)) := by
  let y : ℝ := x / (x + 2)
  have hx2 : 0 < x + 2 := by linarith
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy1 : y < 1 := by
    dsimp [y]
    rw [div_lt_one hx2]
    linarith
  have hmain := Real.log_div_le_sum_range_add hy0 hy1 n
  have heq : (1 + y) / (1 - y) = 1 + x := by
    dsimp [y]
    field_simp [hx2.ne']
    ring
  rw [heq] at hmain
  nlinarith [hmain]

/-- Lower bound for `log(1+x)`: the first `n` odd terms of the same series.
Valid for `0 ≤ x`. -/
private lemma log_one_add_ge_atanh {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n,
          (x / (x + 2)) ^ (2 * i + 1) / ((2 : ℝ) * i + 1)) ≤
      Real.log (1 + x) := by
  let y : ℝ := x / (x + 2)
  have hx2 : 0 < x + 2 := by linarith
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy1 : y < 1 := by
    dsimp [y]
    rw [div_lt_one hx2]
    linarith
  have hmain := Real.sum_range_le_log_div hy0 hy1 n
  have heq : (1 + y) / (1 - y) = 1 + x := by
    dsimp [y]
    field_simp [hx2.ne']
    ring
  rw [heq] at hmain
  nlinarith [hmain]

/-- `sqrt(a·b) < 0.62074208`: verified by `(0.62074208)² > a·b`. -/
private lemma sqrt_ab_lt_62074208 :
    Real.sqrt (aSerre * bSerre) < (62074208 : ℝ) / 100000000 := by
  rw [Real.sqrt_lt']
  · norm_num [aSerre, bSerre]
  · norm_num

/-- Serre's constant `-log((b-a)/4) + gamma*log((a+2*sqrt(a*b)+b)/4)` is negative. -/
theorem serreConstant_neg : serreConstant < 0 := by
  unfold serreConstant
  -- It suffices to show `gamma * log X < log Y` for
  -- X := (a + 2*sqrt(a*b) + b)/4,  Y := (b - a)/4.
  have hmain : gSerre * Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4) <
      Real.log ((bSerre - aSerre) / 4) := by
    -- x2 := (a + 2*(0.62074208) + b)/4 = 1.43497829, an upper bound for X.
    have hXlt : (aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4 <
        (143497829 : ℝ) / 100000000 := by
      have hs := sqrt_ab_lt_62074208
      norm_num [aSerre, bSerre] at hs ⊢
      nlinarith
    have hXpos : 0 < (aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4 := by
      have hb : 0 ≤ Real.sqrt (aSerre * bSerre) := Real.sqrt_nonneg _
      nlinarith [aSerre_pos, bSerre_pos, hb]
    -- u := x2 - 1 > 0, v := Y - 1 > 0 (so x2 = 1+u, Y = 1+v)
    have hu0 : 0 ≤ (43497829 : ℝ) / 100000000 := by norm_num
    have hv0 : 0 ≤ (323723 : ℝ) / 4000000 := by norm_num
    -- Upper rational bound for log x2 = log(1+u), 6 terms of the series.
    have heqU : (143497829 : ℝ) / 100000000 = 1 + (43497829 : ℝ) / 100000000 := by
      norm_num
    have hUgen := log_one_add_le_atanh hu0 6
    have hU : Real.log ((143497829 : ℝ) / 100000000) ≤
        2 * ((∑ i ∈ Finset.range 6,
              (((43497829 : ℝ) / 100000000) / (((43497829 : ℝ) / 100000000) + 2)) ^ (2 * i + 1) /
                ((2 : ℝ) * i + 1)) +
            (((43497829 : ℝ) / 100000000) / (((43497829 : ℝ) / 100000000) + 2)) ^ (2 * 6 + 1) /
              (1 - (((43497829 : ℝ) / 100000000) / (((43497829 : ℝ) / 100000000) + 2)) ^ 2)) := by
      rw [heqU]
      exact hUgen
    -- Lower rational bound for log Y = log(1+v), 4 terms of the series.
    have heqL : (bSerre - aSerre) / 4 = 1 + (323723 : ℝ) / 4000000 := by
      norm_num [aSerre, bSerre]
    have hLgen := log_one_add_ge_atanh hv0 4
    have hL : 2 * (∑ i ∈ Finset.range 4,
          (((323723 : ℝ) / 4000000) / (((323723 : ℝ) / 4000000) + 2)) ^ (2 * i + 1) /
            ((2 : ℝ) * i + 1)) ≤
        Real.log ((bSerre - aSerre) / 4) := by
      rw [heqL]
      exact hLgen
    calc
      gSerre * Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4)
          ≤ gSerre * Real.log ((143497829 : ℝ) / 100000000) := by
            exact mul_le_mul_of_nonneg_left
              (le_of_lt (Real.log_lt_log hXpos hXlt)) (le_of_lt gSerre_pos)
      _ ≤ gSerre * (2 * ((∑ i ∈ Finset.range 6,
              (((43497829 : ℝ) / 100000000) / (((43497829 : ℝ) / 100000000) + 2)) ^ (2 * i + 1) /
                ((2 : ℝ) * i + 1)) +
            (((43497829 : ℝ) / 100000000) / (((43497829 : ℝ) / 100000000) + 2)) ^ (2 * 6 + 1) /
              (1 - (((43497829 : ℝ) / 100000000) / (((43497829 : ℝ) / 100000000) + 2)) ^ 2))) := by
            exact mul_le_mul_of_nonneg_left hU (le_of_lt gSerre_pos)
      _ < 2 * (∑ i ∈ Finset.range 4,
            (((323723 : ℝ) / 4000000) / (((323723 : ℝ) / 4000000) + 2)) ^ (2 * i + 1) /
              ((2 : ℝ) * i + 1)) := by
            norm_num [gSerre]
      _ ≤ Real.log ((bSerre - aSerre) / 4) := hL
  linarith

end Submission.SerreConstantNeg

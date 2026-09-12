import Submission.SerreExample
import Submission.SerreMean
import Submission.SerreLogMoment
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Positivity of the log-moment of Serre's measure (contract A4-num)

Proves `SerreArithmetic.serre_log_moment_pos`:

    0 < ∫ x, log‖(x:ℂ)‖ ∂(serreMeasure gSerre aSerre bSerre)

## Route (exact numbers verified to 40 digits)

1. By `SerreLogMoment.serre_log_moment_eq` the integral equals
   `V := −γ·log X₁ + (1−γ)·log X₂` with
   `X₁ := (a+2√(ab)+b)/(4ab) ≈ 3.72411398`,
   `X₂ := (a+2√(ab)+b)/4 ≈ 1.43497829`.
   Numerically `γ·log X₁ ≈ 0.283325920`, `(1−γ)·log X₂ ≈ 0.283327371`,
   `V ≈ 1.4513·10⁻⁶ > 0` (margin ~1.45·10⁻⁶).
2. It suffices to prove `γ·(upper bound of log X₁) < (1−γ)·(lower bound of
   log X₂)`.  Bracket `√(ab) ∈ (s₁, s₂)` with rationals whose squares bracket
   `ab` (e.g. `s₁ = 0.62074207`, `s₂ = 0.62074208`), yielding rational
   brackets `X₁ ∈ (x₁⁻, x₁⁺)`, `X₂ ∈ (x₂⁻, x₂⁺)` with `x₂⁻ > 1`; by
   monotonicity `log X₁ ≤ log x₁⁺` and `log X₂ ≥ log x₂⁻`.
3. Rational bounds on log at `x₁⁺ ≈ 3.7241` and `x₂⁻ ≈ 1.43498` (> 1): use
   `log r = 2·artanh(t)`, `t = (r−1)/(r+1) ∈ (0,1)`, with the series
   `artanh t = t + t³/3 + t⁵/5 + ⋯` (positive terms): partial sums are LOWER
   bounds; for an UPPER bound add the geometric tail
   `t^(2k+3)/((2k+3)·(1−t²))`.  For `x₁⁺`: `t₁ ≈ 0.57657`, use ≥ 21 terms
   (error ~ t₁⁴³/43 ~ 10⁻¹¹); for `x₂⁻`: `t₂ ≈ 0.17864`, ≥ 7 terms suffice.
   The resulting rational inequality `γ·U₊ < (1−γ)·L₋` has margin ~10⁻⁷ and is
   `norm_num`-checkable (add terms for margin as desired).
4. Finish with `Real.log`/`Real.sqrt` monotonicity and `norm_num`/`nlinarith`
   on rationals; the alternating/artanh bounds are private lemmas.

Useful: `Real.log_lt_log`, `Real.log_le_log`, `Real.sqrt_lt`, `Real.sq_sqrt`,
`Real.log_mul`/`log_div`, `Real.log_pow`, and the power series of log
(`Real.log_eq_tsum`, `Real.sum_log`).

Concretely we use the power-series lemmas
`Real.sum_range_le_log_div` (lower bound on `(1/2)·log((1+x)/(1−x))` by
partial sums of `artanh x`) and `Real.log_div_le_sum_range_add` (upper bound
adding the geometric tail `x^(2n+1)/(1−x²)`) with the artanh substitution
`x = (r−1)/(r+1)`, which gives `(1+x)/(1−x) = r`.
-/

noncomputable section

open scoped Real BigOperators

namespace Submission.SerreLogMomentPos

open Submission.SerreLogMoment
open Submission.Serre
open Submission.SerreExample
open Submission.PotentialDefs

/-- Left bracket of `√(aSerre·bSerre)` (rational). -/
def sqrtLo : ℝ := 0.62074207

/-- Right bracket of `√(aSerre·bSerre)` (rational). -/
def sqrtHi : ℝ := 0.62074208

/-- Rational upper bound of `(a+2√(ab)+b)/(4ab)`. -/
def X1up : ℝ := (aSerre + bSerre + 2 * sqrtHi) / (4 * aSerre * bSerre)

/-- Rational lower bound of `(a+2√(ab)+b)/4`. -/
def X2lo : ℝ := (aSerre + bSerre + 2 * sqrtLo) / 4

/-- artanh variable `(X1up−1)/(X1up+1)`. -/
def u1 : ℝ := (X1up - 1) / (X1up + 1)

/-- artanh variable `(X2lo−1)/(X2lo+1)`. -/
def u2 : ℝ := (X2lo - 1) / (X2lo + 1)

lemma sqrt_ab_le_sqrtHi : Real.sqrt (aSerre * bSerre) ≤ sqrtHi := by
  have hsq : aSerre * bSerre < sqrtHi ^ 2 := by norm_num [aSerre, bSerre, sqrtHi]
  exact le_of_lt ((Real.sqrt_lt' (by norm_num [sqrtHi] : (0 : ℝ) < sqrtHi)).2 hsq)

lemma sqrtLo_le_sqrt_ab : sqrtLo ≤ Real.sqrt (aSerre * bSerre) := by
  have hsq : sqrtLo ^ 2 < aSerre * bSerre := by norm_num [aSerre, bSerre, sqrtLo]
  exact le_of_lt (Real.lt_sqrt_of_sq_lt hsq)

lemma X1up_gt_one : 1 < X1up := by norm_num [X1up, aSerre, bSerre, sqrtHi]
lemma X2lo_gt_one : 1 < X2lo := by norm_num [X2lo, aSerre, bSerre, sqrtLo]
lemma X1up_pos : 0 < X1up := lt_trans zero_lt_one X1up_gt_one
lemma X2lo_pos : 0 < X2lo := lt_trans zero_lt_one X2lo_gt_one

lemma denom_pos : 0 < (4 : ℝ) * aSerre * bSerre := by norm_num [aSerre, bSerre]

lemma u1_nonneg : 0 ≤ u1 := by norm_num [u1, X1up, aSerre, bSerre, sqrtHi]
lemma u1_lt_one : u1 < 1 := by norm_num [u1, X1up, aSerre, bSerre, sqrtHi]
lemma u2_nonneg : 0 ≤ u2 := by norm_num [u2, X2lo, aSerre, bSerre, sqrtLo]
lemma u2_lt_one : u2 < 1 := by norm_num [u2, X2lo, aSerre, bSerre, sqrtLo]

lemma u1_frac : (1 + u1) / (1 - u1) = X1up := by
  rw [u1]
  field_simp [show X1up + 1 ≠ 0 by nlinarith [X1up_pos]]
  ring

lemma u2_frac : (1 + u2) / (1 - u2) = X2lo := by
  rw [u2]
  field_simp [show X2lo + 1 ≠ 0 by nlinarith [X2lo_pos]]
  ring

/-- Upper rational bound on `log X1up`: `log X1up ≤ 2·(19 partial terms + geometric tail)`. -/
lemma upper_bound_log_X1up :
    Real.log X1up ≤
      2 * ((∑ i ∈ Finset.range 19, u1 ^ (2 * i + 1) / (2 * i + 1)) +
        u1 ^ (2 * 19 + 1) / (1 - u1 ^ 2)) := by
  have hu := Real.log_div_le_sum_range_add u1_nonneg u1_lt_one 19
  rw [u1_frac] at hu
  nlinarith

/-- Lower rational bound on `log X2lo`: `2·(6 partial terms) ≤ log X2lo`. -/
lemma lower_bound_log_X2lo :
    2 * (∑ i ∈ Finset.range 6, u2 ^ (2 * i + 1) / (2 * i + 1)) ≤ Real.log X2lo := by
  have hl := Real.sum_range_le_log_div u2_nonneg u2_lt_one 6
  rw [u2_frac] at hl
  nlinarith

/-- The rational core: the interval bound `γ·2·U₊ < (1−γ)·2·L₋` (checked by exact rational arithmetic). -/
lemma rational_ineq :
    gSerre *
        (2 * ((∑ i ∈ Finset.range 19, u1 ^ (2 * i + 1) / (2 * i + 1)) +
          u1 ^ (2 * 19 + 1) / (1 - u1 ^ 2))) <
      (1 - gSerre) * (2 * (∑ i ∈ Finset.range 6, u2 ^ (2 * i + 1) / (2 * i + 1))) := by
  simp [Finset.sum_range_succ]
  norm_num [gSerre, u1, X1up, u2, X2lo, aSerre, bSerre, sqrtLo, sqrtHi]

/-- (A4-num) The log-moment of Serre's measure is strictly positive. -/
theorem serre_log_moment_pos :
    0 < (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂serreMeasure gSerre aSerre bSerre) := by
  rw [serre_log_moment_eq]
  set X1 : ℝ :=
    (aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (4 * aSerre * bSerre) with hX1
  set X2 : ℝ := (aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4 with hX2
  have hX1_le : X1 ≤ X1up := by
    rw [hX1]
    dsimp [X1up]
    rw [div_le_div_iff_of_pos_right denom_pos]
    nlinarith [sqrt_ab_le_sqrtHi]
  have hX2_le : X2lo ≤ X2 := by
    rw [hX2]
    dsimp [X2lo]
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)]
    nlinarith [sqrtLo_le_sqrt_ab]
  have hX1pos : 0 < X1 := by
    rw [hX1]
    have hnum : 0 < aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre := by
      nlinarith [aSerre_pos, bSerre_pos, Real.sqrt_nonneg (aSerre * bSerre)]
    exact div_pos hnum denom_pos
  have hlog1 : Real.log X1 ≤ Real.log X1up := Real.log_le_log hX1pos hX1_le
  have hlog2 : Real.log X2lo ≤ Real.log X2 := Real.log_le_log X2lo_pos hX2_le
  have hg0 : 0 ≤ gSerre := le_of_lt gSerre_pos
  have h1g0 : 0 ≤ 1 - gSerre := sub_nonneg.mpr gSerre_le_one
  have hAg1 : gSerre * Real.log X1 ≤ gSerre * Real.log X1up :=
    mul_le_mul_of_nonneg_left hlog1 hg0
  have hAg2 : (1 - gSerre) * Real.log X2lo ≤ (1 - gSerre) * Real.log X2 :=
    mul_le_mul_of_nonneg_left hlog2 h1g0
  have hBup : gSerre * Real.log X1up ≤
      gSerre * (2 * ((∑ i ∈ Finset.range 19, u1 ^ (2 * i + 1) / (2 * i + 1)) +
        u1 ^ (2 * 19 + 1) / (1 - u1 ^ 2))) :=
    mul_le_mul_of_nonneg_left upper_bound_log_X1up hg0
  have hBlo : (1 - gSerre) * (2 * (∑ i ∈ Finset.range 6, u2 ^ (2 * i + 1) / (2 * i + 1))) ≤
      (1 - gSerre) * Real.log X2lo :=
    mul_le_mul_of_nonneg_left lower_bound_log_X2lo h1g0
  have hchain : gSerre * Real.log X1up < (1 - gSerre) * Real.log X2lo := by
    calc
      gSerre * Real.log X1up ≤
          gSerre * (2 * ((∑ i ∈ Finset.range 19, u1 ^ (2 * i + 1) / (2 * i + 1)) +
            u1 ^ (2 * 19 + 1) / (1 - u1 ^ 2))) := hBup
      _ < (1 - gSerre) * (2 * (∑ i ∈ Finset.range 6, u2 ^ (2 * i + 1) / (2 * i + 1))) :=
            rational_ineq
      _ ≤ (1 - gSerre) * Real.log X2lo := hBlo
  have hpos : 0 < (1 - gSerre) * Real.log X2lo - gSerre * Real.log X1up := by linarith
  norm_num [gSerre] at hAg1 hAg2 hpos ⊢
  linarith

end Submission.SerreLogMomentPos

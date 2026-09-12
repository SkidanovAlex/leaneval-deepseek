import Mathlib
import Submission.S6Core
import Submission.Consts

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex
set_option autoImplicit false

namespace Submission
namespace NumBounds

/-! Lower-bound numerics for the `c`-branch: for a tile level `t` (so that
`q ≤ 2^(t+57)`), the cell threshold `goodCellBound t q` satisfies

    2·goodCellBound t q − 1 ≥ (2^170)⁻¹·√q.

Proof sketch (all constants very loose):  `√q ≥ 2^171` (from `2^400 ≤ q`),
hence `(2^170)⁻¹·√q + 1 ≤ 3·2^-171·√q`; and `2·goodCellBound t q` is shown
`≥ 27·2^-144·√(2^(t+1))`: `√q ≤ 2^28·√(2^(t+1))` (from `q ≤ 2^(t+57)`) and
`η := π·2^(t+11)/q ≥ 3·2^-46` (`π ≥ 3`, `q ≤ 2^(t+57)`), so
`3·2^-171·√q ≤ 3·2^-143·√(2^(t+1)) = 6·2^-144·√(2^(t+1)) ≤ 27·2^-144·√(2^(t+1))
 ≤ (1/2^6)·η^3·√(2^(t+1)) = 2·goodCellBound t q`. -/

theorem goodCellBound_lower {t q : ℕ} (hq : (2 : ℝ) ^ 400 ≤ (q : ℝ))
    (hqt : (q : ℝ) ≤ (2 : ℝ) ^ (t + 57)) :
    ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) + 1 ≤ 2 * Sec3.goodCellBound t q := by
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ 400) hq
  have hq0 : 0 ≤ (q : ℝ) := le_of_lt hqpos
  have hT0 : 0 ≤ (2 : ℝ) ^ (t + 1) := by positivity
  -- A: √q ≥ 2^171
  have hA : (2 : ℝ) ^ 171 ≤ Real.sqrt (q : ℝ) := by
    rw [Real.le_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 171) hq0]
    calc
      ((2 : ℝ) ^ 171) ^ 2 = (2 : ℝ) ^ (171 * 2) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ 342 := by rw [show (171 * 2 : ℕ) = 342 by norm_num]
      _ ≤ (2 : ℝ) ^ 400 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 342 ≤ 400)
      _ ≤ (q : ℝ) := hq
  have hsmall : (1 : ℝ) ≤ ((2 : ℝ) ^ 171)⁻¹ * Real.sqrt (q : ℝ) := by
    calc
      (1 : ℝ) = ((2 : ℝ) ^ 171)⁻¹ * (2 : ℝ) ^ 171 := by
        rw [inv_mul_cancel₀ (pow_ne_zero 171 (by norm_num : (2 : ℝ) ≠ 0))]
      _ ≤ ((2 : ℝ) ^ 171)⁻¹ * Real.sqrt (q : ℝ) := by
        exact mul_le_mul_of_nonneg_left hA (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 171))
  -- Claim 1: LHS ≤ 3·((2^171)⁻¹·√q)
  have hclaim1 : ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) + 1 ≤
      3 * (((2 : ℝ) ^ 171)⁻¹ * Real.sqrt (q : ℝ)) := by
    have hrel : ((2 : ℝ) ^ 170)⁻¹ = 2 * ((2 : ℝ) ^ 171)⁻¹ := by
      have hp : (2 : ℝ) ^ 171 = 2 * (2 : ℝ) ^ 170 := by
        rw [show 171 = 170 + 1 by norm_num]
        rw [pow_succ']
      rw [hp]
      field_simp [pow_ne_zero 170 (by norm_num : (2 : ℝ) ≠ 0)]
    calc
      ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) + 1
          = 2 * (((2 : ℝ) ^ 171)⁻¹ * Real.sqrt (q : ℝ)) + 1 := by
              rw [hrel]
              ring
      _ ≤ 3 * (((2 : ℝ) ^ 171)⁻¹ * Real.sqrt (q : ℝ)) := by nlinarith [hsmall]
  -- B: √q ≤ 2^28 · √(2^(t+1))
  have hBexact : (2 : ℝ) ^ (t + 57) = ((2 : ℝ) ^ 28 * Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 := by
    calc
      (2 : ℝ) ^ (t + 57) = (2 : ℝ) ^ ((t + 1) + 56) := by rw [show t + 57 = (t + 1) + 56 by omega]
      _ = (2 : ℝ) ^ (t + 1) * (2 : ℝ) ^ 56 := by rw [pow_add]
      _ = (Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 * (2 : ℝ) ^ 56 := by
          nth_rewrite 1 [← Real.sq_sqrt hT0]
          rfl
      _ = ((2 : ℝ) ^ 28 * Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 := by
        calc
          (Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 * (2 : ℝ) ^ 56
              = (Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 * ((2 : ℝ) ^ 28) ^ 2 := by
                  rw [show (2 : ℝ) ^ 56 = ((2 : ℝ) ^ 28) ^ 2 by
                    calc
                      (2 : ℝ) ^ 56 = (2 : ℝ) ^ (28 * 2) := by rw [show 56 = 28 * 2 by norm_num]
                      _ = ((2 : ℝ) ^ 28) ^ 2 := by rw [pow_mul]]
          _ = ((2 : ℝ) ^ 28 * Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 := by
              rw [mul_pow]
              ring
  have hB : Real.sqrt (q : ℝ) ≤ (2 : ℝ) ^ 28 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
    have h1 : Real.sqrt (q : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ (t + 57)) := Real.sqrt_le_sqrt hqt
    have h2 : Real.sqrt ((2 : ℝ) ^ (t + 57)) ≤ (2 : ℝ) ^ 28 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · rw [hBexact]
    exact le_trans h1 h2
  -- η-expansion of 2g
  have h2g : 2 * Sec3.goodCellBound t q =
      (1 / (2 ^ 6 : ℝ)) * (((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ)) ^ 3 *
        Real.sqrt (2 ^ (t + 1) : ℝ) := by
    have hg : Sec3.goodCellBound t q =
        (1 / (2 ^ 7 : ℝ)) * (((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ)) ^ 3 *
          Real.sqrt (2 ^ (t + 1) : ℝ) := by
      rw [Sec3.goodCellBound_eq]
      unfold Sec3.cellThresh
      rw [Sec3.eta_eq]
      ring
    calc
      2 * Sec3.goodCellBound t q = 2 * ((1 / (2 ^ 7 : ℝ)) * (((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ)) ^ 3 *
          Real.sqrt (2 ^ (t + 1) : ℝ)) := by rw [hg]
      _ = (1 / (2 ^ 6 : ℝ)) * (((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ)) ^ 3 *
          Real.sqrt (2 ^ (t + 1) : ℝ) := by norm_num; ring
  -- η ≥ 3·(2^46)⁻¹
  have hE : (3 : ℝ) * ((2 : ℝ) ^ 46)⁻¹ ≤ ((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ) := by
    have hrecip : ((2 : ℝ) ^ (t + 57))⁻¹ ≤ (q : ℝ)⁻¹ := by
      have h := one_div_le_one_div_of_le hqpos hqt
      simpa using h
    have hA1 : (3 : ℝ) * (2 : ℝ) ^ (t + 11) / (2 : ℝ) ^ (t + 57) ≤
        (3 : ℝ) * (2 : ℝ) ^ (t + 11) / (q : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hrecip (by positivity : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ (t + 11))
    have hden : (2 : ℝ) ^ (t + 57) = (2 : ℝ) ^ (t + 11) * (2 : ℝ) ^ 46 := by
      rw [show t + 57 = (t + 11) + 46 by omega]
      rw [pow_add]
    have hE0 : (3 : ℝ) * (2 : ℝ) ^ (t + 11) / (2 : ℝ) ^ (t + 57) = (3 : ℝ) * ((2 : ℝ) ^ 46)⁻¹ := by
      rw [div_eq_mul_inv, hden]
      field_simp [pow_ne_zero (t + 11) (by norm_num : (2 : ℝ) ≠ 0)]
    have hpi3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
    calc
      (3 : ℝ) * ((2 : ℝ) ^ 46)⁻¹ = (3 : ℝ) * (2 : ℝ) ^ (t + 11) / (2 : ℝ) ^ (t + 57) := hE0.symm
      _ ≤ (3 : ℝ) * (2 : ℝ) ^ (t + 11) / (q : ℝ) := hA1
      _ = ((2 : ℝ) ^ (t + 11) * (3 : ℝ)) / (q : ℝ) := by ring
      _ ≤ ((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ) := by
          have hb0 : (0 : ℝ) ≤ (2 : ℝ) ^ (t + 11) / (q : ℝ) := by positivity
          calc
            ((2 : ℝ) ^ (t + 11) * (3 : ℝ)) / (q : ℝ) = (2 : ℝ) ^ (t + 11) / (q : ℝ) * 3 := by ring
            _ ≤ (2 : ℝ) ^ (t + 11) / (q : ℝ) * Real.pi := mul_le_mul_of_nonneg_left hpi3 hb0
            _ = ((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ) := by ring
  -- main lower bound: 27·(2^144)⁻¹·√T ≤ 2g
  have hmain : (27 : ℝ) * ((2 : ℝ) ^ 144)⁻¹ * Real.sqrt (2 ^ (t + 1) : ℝ) ≤
      2 * Sec3.goodCellBound t q := by
    have hE3 : ((3 : ℝ) * ((2 : ℝ) ^ 46)⁻¹) ^ 3 ≤
        (((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ)) ^ 3 := by
      exact pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) * ((2 : ℝ) ^ 46)⁻¹) hE 3
    calc
      (27 : ℝ) * ((2 : ℝ) ^ 144)⁻¹ * Real.sqrt (2 ^ (t + 1) : ℝ)
          = (1 / (2 ^ 6 : ℝ)) * (((3 : ℝ) * ((2 : ℝ) ^ 46)⁻¹) ^ 3) * Real.sqrt (2 ^ (t + 1) : ℝ) := by
              have hcoefE : (1 / (2 ^ 6 : ℝ)) * ((3 : ℝ) * ((2 : ℝ) ^ 46)⁻¹) ^ 3 =
                  (27 : ℝ) * ((2 : ℝ) ^ 144)⁻¹ := by norm_num
              rw [← hcoefE]
      _ ≤ (1 / (2 ^ 6 : ℝ)) * ((((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ)) ^ 3) *
          Real.sqrt (2 ^ (t + 1) : ℝ) := by
              calc
                (1 / (2 ^ 6 : ℝ)) * (((3 : ℝ) * ((2 : ℝ) ^ 46)⁻¹) ^ 3) * Real.sqrt (2 ^ (t + 1) : ℝ)
                    = ((1 / (2 ^ 6 : ℝ)) * Real.sqrt (2 ^ (t + 1) : ℝ)) * (((3 : ℝ) * ((2 : ℝ) ^ 46)⁻¹) ^ 3) := by ring
                _ ≤ ((1 / (2 ^ 6 : ℝ)) * Real.sqrt (2 ^ (t + 1) : ℝ)) * ((((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ)) ^ 3) := by
                    exact mul_le_mul_of_nonneg_left hE3 (by positivity : 0 ≤ (1 / (2 ^ 6 : ℝ)) * Real.sqrt (2 ^ (t + 1) : ℝ))
                _ = (1 / (2 ^ 6 : ℝ)) * ((((2 : ℝ) ^ (t + 11) * Real.pi) / (q : ℝ)) ^ 3) * Real.sqrt (2 ^ (t + 1) : ℝ) := by ring
      _ = 2 * Sec3.goodCellBound t q := by
              rw [h2g]
  -- assemble
  calc
    ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) + 1 ≤ 3 * (((2 : ℝ) ^ 171)⁻¹ * Real.sqrt (q : ℝ)) := hclaim1
    _ ≤ 3 * (((2 : ℝ) ^ 171)⁻¹ * ((2 : ℝ) ^ 28 * Real.sqrt (2 ^ (t + 1) : ℝ))) := by
        rw [← mul_assoc, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 3 * ((2 : ℝ) ^ 171)⁻¹)
    _ ≤ (27 : ℝ) * ((2 : ℝ) ^ 144)⁻¹ * Real.sqrt (2 ^ (t + 1) : ℝ) := by
        have hc : 3 * ((2 : ℝ) ^ 171)⁻¹ * (2 : ℝ) ^ 28 ≤ 27 * ((2 : ℝ) ^ 144)⁻¹ := by norm_num
        calc
          3 * (((2 : ℝ) ^ 171)⁻¹ * ((2 : ℝ) ^ 28 * Real.sqrt (2 ^ (t + 1) : ℝ)))
              = (3 * ((2 : ℝ) ^ 171)⁻¹ * (2 : ℝ) ^ 28) * Real.sqrt (2 ^ (t + 1) : ℝ) := by ring
          _ ≤ (27 * ((2 : ℝ) ^ 144)⁻¹) * Real.sqrt (2 ^ (t + 1) : ℝ) := by
              exact mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
    _ ≤ 2 * Sec3.goodCellBound t q := hmain

end NumBounds
end Submission

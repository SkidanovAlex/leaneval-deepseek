import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeAux
import Submission.Work.ZeroDensity.Ingham.AfeSelf.Defs
import Submission.Work.ZeroDensity.Zeta.sinIntegralTailBalanced
import Submission.Work.ZeroDensity.Zeta.sinTailUniform

/-!
# Auxiliary vocabulary for the resonance sum bound

This module fixes the notation used by `afeResonanceSumBound`:

* `afeP t = 2π·N` with `N = afeNt t`, the scaling constant of the balanced
  truncation;
* `afeY t = t / afeP t`, the dual truncation parameter, so that
  `afeMt t = ⌊afeY t⌋`;
* `afeYc t = afeMt t - 1`, the cut between the "main" (finite) part and the
  "tail" of the sawtooth–Fourier sum.

The elementary arithmetic of these quantities for `t ≥ 10^6` is collected here.
-/

namespace Work.ZeroDensity.Ingham.AfeProof

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- `2π·N`, the scaling constant of the balanced truncation `N = afeNt t`. -/
def afeP (t : ℝ) : ℝ := 2 * Real.pi * (afeNt t : ℝ)

/-- The dual truncation parameter `y = t/(2πN)`; then `afeMt t = ⌊y⌋`. -/
def afeY (t : ℝ) : ℝ := t / afeP t

/-- The main/tail cut `⌊y⌋ - 1` of the sawtooth–Fourier sum. -/
def afeYc (t : ℝ) : ℕ := afeMt t - 1

lemma afeP_pos (t : ℝ) : 0 < afeP t := by
  rw [afeP]; have := one_le_afeNt t; positivity

lemma afeP_ge (t : ℝ) : 1 ≤ afeP t := by
  have hN : (1 : ℝ) ≤ (afeNt t : ℝ) := by exact_mod_cast one_le_afeNt t
  rw [afeP]; nlinarith [Real.pi_gt_three]

lemma afeMt_eq (t : ℝ) : afeMt t = ⌊afeY t⌋₊ := by
  rw [afeMt, afeY, afeP]

lemma afeYc_eq (t : ℝ) : afeYc t = ⌊afeY t⌋₊ - 1 := by
  rw [afeYc, afeMt_eq]

lemma afeNt_ge {t : ℝ} (ht : 1000000 ≤ t) : 39 ≤ afeNt t := by
  have hs : (38 : ℝ) ≤ Real.sqrt (t / (2 * Real.pi)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [Real.pi_lt_four, ht]
  have h38 : 38 ≤ ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ := Nat.le_floor hs
  rw [afeNt]; omega

lemma afeNt_pos (t : ℝ) : (0 : ℝ) < (afeNt t : ℝ) := by
  have := one_le_afeNt t; exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)

lemma afeY_mul {t : ℝ} (ht : 1000000 ≤ t) : afeY t * afeP t = t := by
  have hP : afeP t ≠ 0 := by
    rw [afeP]
    have hN : (1 : ℝ) ≤ (afeNt t : ℝ) := by exact_mod_cast one_le_afeNt t
    positivity
  rw [afeY]; field_simp

lemma afeY_ge_N {t : ℝ} (ht : 1000000 ≤ t) : (afeNt t : ℝ) - 2 ≤ afeY t := by
  have hNpos : (0 : ℝ) < (afeNt t : ℝ) := afeNt_pos t
  have hs2 : (Real.sqrt (t / (2 * Real.pi))) ^ 2 = t / (2 * Real.pi) :=
    Real.sq_sqrt (by positivity)
  have hs1 : (afeNt t : ℝ) - 1 ≤ Real.sqrt (t / (2 * Real.pi)) := by
    rw [afeNt]; push_cast
    have := Nat.floor_le (Real.sqrt_nonneg (t / (2 * Real.pi)))
    linarith
  have hY : afeY t = (Real.sqrt (t / (2 * Real.pi))) ^ 2 / (afeNt t : ℝ) := by
    rw [afeY, afeP, hs2]; ring
  have hsq : (0 : ℝ) ≤ (afeNt t : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (afeNt t : ℝ) := by exact_mod_cast one_le_afeNt t
    linarith
  have hnum : ((afeNt t : ℝ) - 1) ^ 2 ≤ (Real.sqrt (t / (2 * Real.pi))) ^ 2 := by
    nlinarith [hs1, hsq]
  rw [hY, le_div_iff₀ hNpos]
  have hkey : ((afeNt t : ℝ) - 2) * (afeNt t : ℝ)
      ≤ ((afeNt t : ℝ) - 1) ^ 2 := by nlinarith
  nlinarith [hkey, hnum]

lemma afeY_le_N {t : ℝ} (ht : 1000000 ≤ t) : afeY t ≤ (afeNt t : ℝ) := by
  have hNpos : (0 : ℝ) < (afeNt t : ℝ) := afeNt_pos t
  have hs2 : (Real.sqrt (t / (2 * Real.pi))) ^ 2 = t / (2 * Real.pi) :=
    Real.sq_sqrt (by positivity)
  have hslt : Real.sqrt (t / (2 * Real.pi)) < (afeNt t : ℝ) := by
    rw [afeNt]; push_cast; exact Nat.lt_floor_add_one _
  have hs0 : (0 : ℝ) ≤ Real.sqrt (t / (2 * Real.pi)) := Real.sqrt_nonneg _
  have hY : afeY t = (Real.sqrt (t / (2 * Real.pi))) ^ 2 / (afeNt t : ℝ) := by
    rw [afeY, afeP, hs2]; ring
  rw [hY, div_le_iff₀ hNpos]
  nlinarith [hslt, hs0]

lemma afeY_pos {t : ℝ} (ht : 1000000 ≤ t) : 0 < afeY t := by
  have h1 := afeY_ge_N ht
  have h2 : (39 : ℝ) ≤ (afeNt t : ℝ) := by exact_mod_cast afeNt_ge ht
  linarith

lemma afeY_ge {t : ℝ} (ht : 1000000 ≤ t) : 3 ≤ afeY t := by
  have h1 := afeY_ge_N ht
  have h2 : (39 : ℝ) ≤ (afeNt t : ℝ) := by exact_mod_cast afeNt_ge ht
  linarith

lemma logY_bound {t : ℝ} (ht : 1000000 ≤ t) :
    Real.log (afeY t) + 1 ≤ 10 * (afeP t) ^ (1 / 2 : ℝ) := by
  have hypos : 0 < afeY t := afeY_pos ht
  have hyle : afeY t ≤ (afeNt t : ℝ) := afeY_le_N ht
  have hylog : Real.log (afeY t) ≤ 2 * ((afeNt t : ℝ)) ^ (1 / 2 : ℝ) := by
    refine (Real.log_le_log hypos hyle).trans ?_
    have hN0 : (0 : ℝ) ≤ (afeNt t : ℝ) := le_of_lt (afeNt_pos t)
    have h := Real.log_le_rpow_div (x := (afeNt t : ℝ)) (ε := (1 / 2 : ℝ)) hN0
      (by norm_num)
    have h' : ((afeNt t : ℝ)) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)
        = 2 * ((afeNt t : ℝ)) ^ (1 / 2 : ℝ) := by ring
    linarith [h, h'.ge, h'.le]
  have hroot : (1 : ℝ) ≤ ((afeNt t : ℝ)) ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num)
      (show (1 : ℝ) ≤ (afeNt t : ℝ) by exact_mod_cast one_le_afeNt t)
      (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)
    simpa using h
  have hroot2 : ((afeNt t : ℝ)) ^ (1 / 2 : ℝ) ≤ (afeP t) ^ (1 / 2 : ℝ) := by
    refine Real.rpow_le_rpow (le_of_lt (afeNt_pos t)) ?_ (by norm_num)
    rw [afeP]
    nlinarith [Real.pi_gt_three, le_of_lt (afeNt_pos t)]
  have hP0 : (0 : ℝ) ≤ (afeP t) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt (afeP_pos t)) _
  calc Real.log (afeY t) + 1 ≤ 2 * ((afeNt t : ℝ)) ^ (1 / 2 : ℝ) + 1 := by linarith
    _ ≤ 3 * ((afeNt t : ℝ)) ^ (1 / 2 : ℝ) := by linarith
    _ ≤ 3 * (afeP t) ^ (1 / 2 : ℝ) := by linarith
    _ ≤ 10 * (afeP t) ^ (1 / 2 : ℝ) := by linarith

lemma afeYc_succ {t : ℝ} (ht : 1000000 ≤ t) : afeYc t + 1 = afeMt t := by
  have h3 : 3 ≤ afeMt t := by
    rw [afeMt_eq]; exact Nat.le_floor (afeY_ge ht)
  rw [afeYc]; omega

/-- `(afeYc t : ℝ) + 1 = ⌊afeY t⌋₊`. -/
lemma afeYc_cast_add_one {t : ℝ} (ht : 1000000 ≤ t) :
    (afeYc t : ℝ) + 1 = (⌊afeY t⌋₊ : ℝ) := by
  have h1 : 1 ≤ afeMt t := by
    rw [afeMt_eq]
    exact Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ afeY t from le_trans (by norm_num) (afeY_ge ht))
  rw [afeYc, Nat.cast_sub h1, Nat.cast_one, afeMt_eq]
  ring

/-- The main part of the sum stays strictly to the left of `t`. -/
lemma afeYc_lt {t : ℝ} (ht : 1000000 ≤ t) :
    ∀ i ∈ Finset.range (afeYc t), ((i : ℝ) + 1) < afeY t := by
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 : ((i : ℝ) + 1) ≤ (afeYc t : ℝ) := by
    have : i + 1 ≤ afeYc t := by omega
    exact_mod_cast this
  have h2 : (afeYc t : ℝ) + 1 ≤ afeY t := by
    rw [afeYc_cast_add_one ht]
    exact Nat.floor_le (le_of_lt (afeY_pos ht))
  linarith

/-- Norm of the index power on the critical line. -/
lemma norm_idx_pow (t : ℝ) (i : ℕ) :
    ‖(((i : ℝ) + 1 : ℂ)) ^ (cls t - 1)‖ = ((i : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hbase : (((i : ℝ) + 1 : ℂ)) = ((((i : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  congr 1
  simp only [Complex.sub_re, Complex.one_re, cls_re]
  norm_num

end

end Work.ZeroDensity.Ingham.AfeProof

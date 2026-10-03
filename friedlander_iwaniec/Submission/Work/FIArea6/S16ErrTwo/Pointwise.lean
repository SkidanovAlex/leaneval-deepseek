import Mathlib
import Submission.Work.FIArea6.S16ErrTwo.Defs
import Submission.Work.FIArea7.LogFacArg

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The sum of `|fcoeff k|` over `|k| ≤ M` is `log 16 + 2(1 + log M)`. -/
lemma fcoeff_abs_sum_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc (-(((M : ℕ) : ℤ))) (((M : ℕ) : ℤ)), |Work.FIArea6.fcoeff k|
      ≤ Real.log 16 + 2 * (1 + Real.log (M : ℝ)) :=
  Work.FIArea6.fcoeff_sum_le M hM

/-- `‖logFac6Series z₁ z₂ (Kcut X)‖ ≤ 8 + 8 log(2+X)`. -/
lemma series_norm_le (X : ℕ) (hX : 1 ≤ X) (z1 z2 : GaussianInt) :
    ‖Work.FIArea7.logFac6Series z1 z2 (Kcut X)‖ ≤ 8 + 8 * Real.log (2 + X) := by
  rw [← Work.FIArea6.sc_logFac6Series_eq_sum_fcoeff X z1 z2]
  have hI : Finset.Icc (-(2 * (Kcut X : ℤ))) (2 * (Kcut X : ℤ))
      = Finset.Icc (-(((2 * Kcut X : ℕ) : ℤ))) (((2 * Kcut X : ℕ) : ℤ)) := by
    rw [show (2 : ℤ) * (Kcut X : ℤ) = ((2 * Kcut X : ℕ) : ℤ) by push_cast; ring]
  rw [hI]
  have hstep : ‖∑ k ∈ Finset.Icc (-(((2 * Kcut X : ℕ) : ℤ))) (((2 * Kcut X : ℕ) : ℤ)),
        (Work.FIArea6.fcoeff k : ℂ) * (psiK k z1 * star (psiK k z2))‖
      ≤ ∑ k ∈ Finset.Icc (-(((2 * Kcut X : ℕ) : ℤ))) (((2 * Kcut X : ℕ) : ℤ)),
          |Work.FIArea6.fcoeff k| := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro k _
    calc ‖(Work.FIArea6.fcoeff k : ℂ) * (psiK k z1 * star (psiK k z2))‖
        = |Work.FIArea6.fcoeff k| * (‖psiK k z1‖ * ‖psiK k z2‖) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
      _ ≤ |Work.FIArea6.fcoeff k| * (1 * 1) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul (Work.FIArea6.S16_psiK_le_one k z1)
            (Work.FIArea6.S16_psiK_le_one k z2) (norm_nonneg _) (by norm_num)
      _ = |Work.FIArea6.fcoeff k| := by ring
  refine le_trans hstep ?_
  · have hXpos : 0 < X := lt_of_lt_of_le Nat.zero_lt_one hX
    have hK1 : 1 ≤ 2 * Kcut X := by
      rw [Work.FIArea6.Kcut]
      exact le_trans (Nat.one_le_pow 3 X hXpos) (Nat.le_mul_of_pos_left _ (by norm_num))
    have hf := fcoeff_abs_sum_le (2 * Kcut X) hK1
    have hlog16 : Real.log 16 ≤ 4 := by
      have h2 : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        norm_num
      have h3 := Real.log_two_lt_d9
      linarith
    have hle : Real.log (((2 * Kcut X : ℕ) : ℝ)) ≤ 2 + 3 * Real.log (2 + X) := by
      have hX0 : (0 : ℝ) < X := by exact_mod_cast hXpos
      have hcast : (((2 * Kcut X : ℕ) : ℝ)) = 2 * (X : ℝ) ^ 3 := by
        rw [show Kcut X = X ^ 3 from rfl]
        push_cast
        ring
      rw [hcast, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      have hlogX : Real.log (X : ℝ) ≤ Real.log (2 + X) := Real.log_le_log hX0 (by linarith)
      push_cast
      linarith
    have hlog1 : 1 ≤ Real.log (2 + X) := by
      have h1 : Real.log 3 ≤ Real.log (2 + X) := by
        apply Real.log_le_log (by norm_num)
        have : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
        linarith
      have h2 : (1 : ℝ) ≤ Real.log 3 := by
        have := Real.exp_one_lt_three
        have h := Real.log_le_log (Real.exp_pos 1) this.le
        rwa [Real.log_exp] at h
      linarith
    linarith

/-- The norm of the product: `√|z₁z₂|² = ‖z₁‖‖z₂‖`. -/
lemma sqrt_gnorm_mul_eq (z1 z2 : GaussianInt) :
    Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ := by
  rw [← Work.FIArea4.crude_norm_toComplex_eq_sqrt (z1 * z2), GaussianInt.toComplex_mul, norm_mul]

/-- On the support of a round-6 coefficient, `|z₁z₂| ≤ 2N`. -/
lemma gnorm_mul_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 z2 : GaussianInt}
    (hz1 : β z1 ≠ 0) (hz2 : β z2 ≠ 0) :
    Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ≤ 2 * Pa.N := by
  have hg1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * Pa.N := sc_gnorm_le_two_N hβ hz1
  have hg2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * Pa.N := sc_gnorm_le_two_N hβ hz2
  have hgmul : ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
      = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    rw [Work.FIArea6b.gnorm_mul]; push_cast; ring
  have hN1 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  rw [Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  rw [hgmul]
  nlinarith

/-- `|Δ(z₁,z₂)| ≤ |z₁z₂|`. -/
lemma absDelta_le_sqrt_gnorm (z1 z2 : GaussianInt) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
  rw [sqrt_gnorm_mul_eq]
  by_cases hD : Work.FIPlan.Delta z1 z2 = 0
  · have h0 : Work.FIPlan.absDelta z1 z2 = 0 := by rw [Work.FIPlan.absDelta, hD]; simp
    rw [h0]
    simp only [Nat.cast_zero]
    positivity
  · rw [Work.FIArea7.LogFacArg.absDelta_eq_norm_mul_abs_sin hD]
    have hsin : |Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)| ≤ 1 := Real.abs_sin_le_one _
    have h1 : (0 : ℝ) ≤ ‖(z1 : ℂ)‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖(z2 : ℂ)‖ := norm_nonneg _
    have h := mul_le_mul_of_nonneg_left hsin (mul_nonneg h1 h2)
    rwa [mul_one] at h

/-- `|logFac6 z₁ z₂| ≤ log(16N)` on the support of a round-6 coefficient. -/
lemma logFac6_abs_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 z2 : GaussianInt}
    (hz1 : β z1 ≠ 0) (hz2 : β z2 ≠ 0) :
    |Work.FITop4.logFac6 z1 z2| ≤ Real.log (16 * Pa.N) := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have htarget : (0 : ℝ) ≤ Real.log (16 * Pa.N) := Real.log_nonneg (by linarith)
  rw [Work.FITop4.logFac6]
  by_cases hg0 : Work.FIPlan.gnorm (z1 * z2) = 0
  · rw [hg0]
    simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_div, Real.log_zero, abs_zero]
    linarith
  · have hsqrtpos : 0 < Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (by positivity)
    by_cases hD : Work.FIPlan.absDelta z1 z2 = 0
    · rw [hD]
      simp only [Nat.cast_zero, div_zero, Real.log_zero, abs_zero]
      linarith
    · have hD1n : 1 ≤ Work.FIPlan.absDelta z1 z2 := Nat.one_le_iff_ne_zero.mpr hD
      have hD1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hD1n
      have hDpos : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
      have hsqrt := gnorm_mul_le hβ hz1 hz2
      have hDle := absDelta_le_sqrt_gnorm z1 z2
      have harg_ge : 8 ≤ 8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
        rw [le_div_iff₀ hDpos]
        nlinarith
      have harg_le : 8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 16 * Pa.N := by
        rw [div_le_iff₀ hDpos]
        nlinarith
      have hupper : Real.log (8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ≤ Real.log (16 * Pa.N) :=
        Real.log_le_log (by linarith) harg_le
      have hlower : 0 ≤ Real.log (8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) := Real.log_nonneg (by linarith)
      rw [abs_of_nonneg hlower]
      exact hupper

end

end Work.FIArea6.S16ErrTwo

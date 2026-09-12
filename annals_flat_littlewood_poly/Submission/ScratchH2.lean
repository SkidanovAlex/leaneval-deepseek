import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3H_deriv

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission.Sec3H

lemma iteratedDeriv_eθ (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => Sec3.eθ y) x = Complex.I ^ k * Sec3.eθ x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun y : ℝ => Sec3.eθ y) = fun y : ℝ => Complex.I ^ k * Sec3.eθ y := by
        funext y
        exact ih y
      rw [hfun]
      have hθ := eθ_hasDerivAt x
      have hc := hθ.const_mul (Complex.I ^ k)
      have hv := hc.deriv
      rw [hv]
      rw [← mul_assoc]
      rw [← pow_succ]

lemma eθ2_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Sec3.eθ (2 * y)) (((2 : ℂ) * Complex.I) * Sec3.eθ (2 * x)) x := by
  have hφ : HasDerivAt (fun y : ℝ => 2 * y) (2 : ℝ) x := by
    simpa using hasDerivAt_const_mul (x := x) (c := (2 : ℝ))
  have hθ := eθ_hasDerivAt (2 * x)
  have hc := hθ.scomp x hφ
  change HasDerivAt (fun y : ℝ => Sec3.eθ (2 * y))
      ((2 : ℝ) • (Complex.I * Sec3.eθ (2 * x))) x at hc
  have hsmul : (2 : ℝ) • (Complex.I * Sec3.eθ (2 * x)) = ((2 : ℂ) * Complex.I) * Sec3.eθ (2 * x) := by
    rw [Algebra.smul_def]
    change ((2 : ℝ) : ℂ) * (Complex.I * Sec3.eθ (2 * x)) = ((2 : ℂ) * Complex.I) * Sec3.eθ (2 * x)
    norm_num
    ring
  exact hc.congr_deriv hsmul

lemma iteratedDeriv_eθ2 (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => Sec3.eθ (2 * y)) x = ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun y : ℝ => Sec3.eθ (2 * y)) =
          fun y : ℝ => ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * y) := by
        funext y
        exact ih y
      rw [hfun]
      have hθ := eθ2_hasDerivAt x
      have hc := hθ.const_mul (((2 : ℂ) * Complex.I) ^ k)
      have hv := hc.deriv
      rw [hv]
      rw [← mul_assoc]
      rw [← pow_succ]

/-- norm of iterated derivatives of eθ: ‖I^i · eθ x‖ = 1 -/
lemma norm_iteratedDeriv_eθ (i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (fun y : ℝ => Sec3.eθ y) x‖ = 1 := by
  rw [iteratedDeriv_eθ]
  rw [norm_mul]
  rw [norm_pow, Complex.norm_I]
  rw [Sec3.norm_eθ]
  norm_num

/-- ‖(2I)^i · eθ(2x)‖ = 2^i -/
lemma norm_iteratedDeriv_eθ2 (i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (fun y : ℝ => Sec3.eθ (2 * y)) x‖ = (2 : ℝ) ^ i := by
  rw [iteratedDeriv_eθ2]
  rw [norm_mul]
  rw [norm_pow]
  rw [norm_mul, Complex.norm_I]
  norm_num
  rw [Sec3.norm_eθ]

end Submission.Sec3H

import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3H_deriv

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission.Sec3H

lemma beta_iter_deriv_le (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (beta t) x‖ ≤ 1 / 2 ^ (9 * k) := by
  unfold beta
  rw [iteratedDeriv_const_mul_field]
  rw [norm_scale_mul]
  rw [thetaPoly_eval_eq_iteratedDeriv_scaled]
  have hT0 : 0 < (T t : ℝ) := by
    have h : 0 < 2 ^ (t + 10) := pow_pos (by norm_num) (t + 10)
    exact_mod_cast h
  rw [norm_inv_pow_mul hT0.le]
  have hdeg : (RudinShapiro.Q t).natDegree ≤ 2 ^ t :=
    (RudinShapiro.Q_natDegree_le t).trans (Nat.sub_le (2 ^ t) 1)
  have hSnorm : ‖(thetaPoly (RudinShapiro.Q t) k).eval (Sec3.eθ (x / (T t : ℝ)))‖ ≤
      ((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ) := by
    exact thetaPoly_eval_norm_le (P := RudinShapiro.Q t) hdeg
      (Real.sqrt (2 ^ (t + 1) : ℝ)) (RudinShapiro.norm_Q_eval_le t) k (Sec3.eθ (x / (T t : ℝ)))
      (Sec3.norm_eθ (x / (T t : ℝ)))
  have hTinv0 : 0 ≤ ((T t : ℝ)⁻¹) ^ k := by positivity
  have hscale0 : 0 ≤ scale t := scale_nonneg t
  have hle : scale t * (((T t : ℝ)⁻¹) ^ k * ‖(thetaPoly (RudinShapiro.Q t) k).eval (Sec3.eθ (x / (T t : ℝ)))‖) ≤
      scale t * (((T t : ℝ)⁻¹) ^ k * (((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ))) := by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSnorm hTinv0) hscale0
  exact le_trans hle (by
    have h' : scale t * (((T t : ℝ)⁻¹) ^ k * (((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ)))
        = scale t * ((T t : ℝ)⁻¹) ^ k * (((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ)) := by ring
    rw [h']
    exact alpha_bound_aux t k)

end Submission.Sec3H

import Mathlib
import Submission.Work.C7.xdefs

/-!
# Area C7 — the fifth pullback `B₅∘y = (x/(x-1))·J`
-/

noncomputable section

namespace Work.C7

open PowerSeries
open Submission.CDTPlan

/-- `yps = x²/(x-1)`. -/
lemma yps_sq_eq_c7 : yps = (X : PowerSeries ℚ) ^ 2 * (X - 1)⁻¹ := by
  rw [yps, Submission.CDT.sympY, Submission.CDT.sympPhi]
  ring

lemma yps_ne_zero_c7 : yps ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.coeff 2) h
  rw [yps, Submission.CDT.coeff_sympY_two] at hc
  norm_num at hc

lemma Xs_sub_one_ne_zero_c7 : (X - 1 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.coeff 0) h
  rw [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_one] at hc
  norm_num at hc

lemma B5_eq_X_mul_K5_c7 : Submission.CDTPlan.B5 = (X : PowerSeries ℚ) * K5 := by
  apply PowerSeries.ext
  intro n
  rw [show (X : PowerSeries ℚ) * K5 = X ^ 1 * K5 by rw [pow_one],
    PowerSeries.coeff_X_pow_mul']
  rcases n with _ | n
  · rw [if_neg (by omega : ¬ (1 : ℕ) ≤ 0)]
    simp [K5, Submission.CDTPlan.B5]
  · rw [if_pos (by omega : (1 : ℕ) ≤ n + 1), show (n + 1 - 1) = n by omega, K5,
      PowerSeries.coeff_mk]

/-- **The fifth pullback**: `B₅∘y = (x/(x-1))·J`. -/
theorem g4_form_c7 : g 4 = (X * (X - 1)⁻¹) * Jps := by
  show (pureB 4).subst yps = _
  have h4 : pureB 4 = Submission.CDTPlan.B5 := by simp [pureB]
  rw [h4, B5_eq_X_mul_K5_c7,
    PowerSeries.subst_mul (a := Submission.CDT.sympY) Submission.CDT.sympY_hasSubst,
    PowerSeries.subst_X (a := Submission.CDT.sympY) Submission.CDT.sympY_hasSubst]
  rw [Jps, show Submission.CDT.sympY = (X : PowerSeries ℚ) * (X * (X - 1)⁻¹) by
        rw [Submission.CDT.sympY, Submission.CDT.sympPhi]]
  have harg : (X : PowerSeries ℚ) * (X * (X - 1)⁻¹) = X ^ 2 * (X - 1)⁻¹ := by ring
  rw [harg, yps_sq_eq_c7]
  ring

end Work.C7

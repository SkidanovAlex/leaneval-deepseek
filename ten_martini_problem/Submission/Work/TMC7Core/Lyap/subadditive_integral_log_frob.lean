import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one

/-!
# Subadditivity of `n ↦ ∫₀¹ log ‖A_n(x)‖_F dx`

The transfer cocycle satisfies `A_{m+n}(x) = A_m(x + nα) · A_n(x)` (`iterC_add`).  Since `frob` is
submultiplicative (`frob_mul_le`) and every `A_n(x)` has determinant `1`, hence Frobenius norm
`≥ √2 > 0` (`frob_sqrt_two_le_of_det_one`), we get the pointwise estimate

`log ‖A_{m+n}(x)‖_F ≤ log ‖A_m(x + nα)‖_F + log ‖A_n(x)‖_F`.

Integrating over `[0,1]` and using that `A_m` is `1`-periodic in `x` (so the integral of
`x ↦ log ‖A_m(x + nα)‖_F` equals that of `x ↦ log ‖A_m(x)‖_F`) yields Fekete's subadditivity
inequality for `n ↦ ∫₀¹ log ‖A_n(x)‖_F dx`.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Work.TMC7Core.Lyap

/-- Every iterate of the transfer cocycle has Frobenius norm at least `√2`, hence positive. -/
theorem frob_iterC_pos (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    0 < frob (iterC α lam E n x) :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num))
    (Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam E n x))

/-- `frob` is continuous: it is Mathlib's Frobenius norm on matrices. -/
theorem continuous_frob : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A) := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A) = fun A => ‖A‖ := by
    funext A; exact Cocycle.frob_eq_norm A
  rw [h]; exact continuous_norm

/-- `x ↦ log ‖A_n(x)‖_F` is continuous (the norm is bounded below by `√2 > 0`). -/
theorem continuous_log_frob_iterC (α lam : ℝ) (E : ℂ) (n : ℕ) :
    Continuous (fun x : ℝ => Real.log (frob (iterC α lam E n x))) :=
  (continuous_frob.comp (continuous_iterC α lam E n)).log
    fun x => ne_of_gt (frob_iterC_pos α lam E n x)

/-- Since `x ↦ log ‖A_m(x)‖_F` is `1`-periodic, shifting its argument does not change its
integral over a full period `[0,1]`. -/
theorem log_frob_integral_shift (α lam : ℝ) (E : ℂ) (m : ℕ) (c : ℝ) :
    (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E m (x + c))))
      = ∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E m x)) := by
  have hper : Function.Periodic (fun x : ℝ => Real.log (frob (iterC α lam E m x))) 1 := by
    intro x
    show Real.log (frob (iterC α lam E m (x + 1))) = Real.log (frob (iterC α lam E m x))
    rw [iterC_periodic]
  trans ∫ x in (0 : ℝ) + c..1 + c, (fun y : ℝ => Real.log (frob (iterC α lam E m y))) x
  · exact intervalIntegral.integral_comp_add_right
      (fun y : ℝ => Real.log (frob (iterC α lam E m y))) c
  · rw [zero_add, show (1 : ℝ) + c = c + 1 by ring]
    simpa using hper.intervalIntegral_add_eq c 0

theorem subadditive_integral_log_frob (α lam : ℝ) (E : ℂ) : Subadditive (fun n : ℕ => ∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E n x))) := by
  intro m n
  have hint : ∀ k : ℕ,
      IntervalIntegrable (fun x : ℝ => Real.log (frob (iterC α lam E k x))) volume (0 : ℝ) 1 :=
    fun k => (continuous_log_frob_iterC α lam E k).intervalIntegrable 0 1
  have hshift : IntervalIntegrable
      (fun x : ℝ => Real.log (frob (iterC α lam E m (x + (n : ℝ) * α)))) volume (0 : ℝ) 1 :=
    ((continuous_log_frob_iterC α lam E m).comp
      (continuous_id.add continuous_const)).intervalIntegrable 0 1
  have h1 : (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (m + n) x)))
      ≤ ∫ x in (0 : ℝ)..1, (Real.log (frob (iterC α lam E m (x + (n : ℝ) * α)))
          + Real.log (frob (iterC α lam E n x))) := by
    refine intervalIntegral.integral_mono (by norm_num) (hint (m + n)) (hshift.add (hint n)) ?_
    intro x
    have hA : 0 < frob (iterC α lam E m (x + (n : ℝ) * α)) := frob_iterC_pos α lam E m _
    have hB : 0 < frob (iterC α lam E n x) := frob_iterC_pos α lam E n x
    have hAB : 0 < frob (iterC α lam E (m + n) x) := frob_iterC_pos α lam E (m + n) x
    have hle : frob (iterC α lam E (m + n) x)
        ≤ frob (iterC α lam E m (x + (n : ℝ) * α)) * frob (iterC α lam E n x) := by
      rw [iterC_add]
      exact Cocycle.frob_mul_le _ _
    calc Real.log (frob (iterC α lam E (m + n) x))
        ≤ Real.log (frob (iterC α lam E m (x + (n : ℝ) * α)) * frob (iterC α lam E n x)) :=
          Real.log_le_log hAB hle
      _ = Real.log (frob (iterC α lam E m (x + (n : ℝ) * α)))
            + Real.log (frob (iterC α lam E n x)) :=
          Real.log_mul (ne_of_gt hA) (ne_of_gt hB)
  rw [intervalIntegral.integral_add hshift (hint n)] at h1
  rw [log_frob_integral_shift α lam E m ((n : ℝ) * α)] at h1
  exact h1

end Work.TMC7Core.Lyap

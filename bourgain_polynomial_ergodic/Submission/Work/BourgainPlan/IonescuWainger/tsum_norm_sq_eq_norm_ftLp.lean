import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped lp BigOperators ENNReal

/-- Parseval for the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary: the squared `ℓ²`-norm of a square-summable
sequence equals the squared `L²`-norm of its Fourier transform `ftLp h hh`. -/
theorem tsum_norm_sq_eq_norm_ftLp {h : ℤ → ℂ} (hh : Memℓp h 2) :
    ∑' n : ℤ, ‖h n‖ ^ 2 = ‖ftLp h hh‖ ^ 2 := by
  -- `ftLp` is the inverse of the Hilbert-basis coordinate map `repr`, an isometry.
  have hnorm : ‖ftLp h hh‖ = ‖(⟨h, hh⟩ : lp (fun _ : ℤ => ℂ) 2)‖ := by
    rw [ftLp]
    exact (fourierBasis (T := 1)).repr.symm.norm_map _
  rw [hnorm]
  -- `ℓ²`-norm computed coefficientwise.
  rw [show (∑' n : ℤ, ‖h n‖ ^ 2)
        = ∑' n : ℤ, ‖((⟨h, hh⟩ : lp (fun _ : ℤ => ℂ) 2)) n‖ ^ ((2 : ℝ≥0∞).toReal) by
    simp]
  rw [← lp.norm_rpow_eq_tsum (show 0 < (2 : ℝ≥0∞).toReal by simp)]
  simp

end Work.BourgainPlan.IonescuWainger

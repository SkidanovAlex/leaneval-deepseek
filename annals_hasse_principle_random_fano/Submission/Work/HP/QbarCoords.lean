import Mathlib
import Submission.Work.HP.JcVolDefs

/-!
# Coordinate form of the `qbar` integral

The integrand of `Work.HP.IntegralQbarPow` lives on `EuclideanSpace ℝ (Fin 2)`.  This file
transports the integral to the coordinate space `ℝ × ℝ`, where it becomes the explicit
two-dimensional integral of `qbCo`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Work.HP

/-- The integrand of `IntegralQbarPow`, transported to coordinates `ℝ × ℝ`:
`(x,y) ↦ (√(max x² y²)) ^ d` on the unit square `[-1,1]²` and `0` outside. -/
def qbCo (d : ℕ) (p : ℝ × ℝ) : ℝ :=
  if max (p.1 ^ 2) (p.2 ^ 2) ≤ 1 then (Real.sqrt (max (p.1 ^ 2) (p.2 ^ 2))) ^ d else 0

lemma qbar_toLp_finTwoArrow (p : ℝ × ℝ) :
    qbar ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) (MeasurableEquiv.finTwoArrow.symm p))
      = max (p.1 ^ 2) (p.2 ^ 2) := by
  simp [qbar, MeasurableEquiv.finTwoArrow]

/-- The integral of `IntegralQbarPow`, written in coordinates on `ℝ × ℝ`. -/
theorem qbar_integral_eq_prod (d : ℕ) :
    (∫ u : EuclideanSpace ℝ (Fin 2), (if qbar u ≤ 1 then (Real.sqrt (qbar u)) ^ d else 0))
    = ∫ p : ℝ × ℝ, qbCo d p := by
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).integral_comp'
        (f := MeasurableEquiv.toLp 2 (Fin 2 → ℝ))]
  rw [← (MeasureTheory.volume_preserving_finTwoArrow ℝ).symm.integral_comp'
        (fun x : Fin 2 → ℝ =>
          (if qbar ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) x) ≤ 1
            then (Real.sqrt (qbar ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) x))) ^ d else 0))]
  simp only [qbCo]
  apply integral_congr_ae
  filter_upwards with p
  rw [qbar_toLp_finTwoArrow p]

end Work.HP

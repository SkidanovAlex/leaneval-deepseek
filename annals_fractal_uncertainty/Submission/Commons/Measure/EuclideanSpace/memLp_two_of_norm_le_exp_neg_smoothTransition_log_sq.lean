import Mathlib.MeasureTheory.Function.L2Space
import Submission.Commons.Measure.EuclideanSpace.integrable_exp_neg_smoothTransition_log_sq

set_option linter.unusedVariables false

namespace Commons.Measure.EuclideanSpace

open MeasureTheory

/-- The pointwise bound `‖f x‖ ≤ C * exp(-(c * χ * r))` together with the integrability of
`x ↦ exp(-(2 c * χ * r))` implies that `f` belongs to `L²`. -/
theorem memLp_two_of_norm_le_exp_neg_smoothTransition_log_sq (d : ℕ) {C c : ℝ} (hC : 0 ≤ C)
    (hc : 0 < c) {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (h : ∀ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ≤ C * Real.exp (-(c *
      (Real.smoothTransition (‖x‖ / 5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))))) :
    MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
  have h2c : (0 : ℝ) < 2 * c := by linarith
  -- Integrability of the exponential with constant `2 * c`.
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(2 * c * (Real.smoothTransition (‖x‖ / 5 - 1) *
        (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2)))))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    integrable_exp_neg_smoothTransition_log_sq d (c := 2 * c) h2c
  -- Pointwise identity: the square of the exponential equals the `2 * c` exponential.
  have hsq : ∀ x : EuclideanSpace ℝ (Fin d),
      (Real.exp (-(c * (Real.smoothTransition (‖x‖ / 5 - 1) *
          (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))))) ^ 2 =
      Real.exp (-(2 * c * (Real.smoothTransition (‖x‖ / 5 - 1) *
          (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2)))) := by
    intro x
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hint_sq : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (Real.exp (-(c * (Real.smoothTransition (‖x‖ / 5 - 1) *
          (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))))) ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    hint.congr (Filter.Eventually.of_forall fun x => (hsq x).symm)
  -- The exponential belongs to `L²`.
  have hmem : MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(c * (Real.smoothTransition (‖x‖ / 5 - 1) *
        (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))))) 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    (memLp_two_iff_integrable_sq
      (measurable_exp_neg_smoothTransition_log_sq d c).aestronglyMeasurable).2 hint_sq
  -- Multiplying by the constant preserves membership in `L²`.
  have hmemC : MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      C * Real.exp (-(c * (Real.smoothTransition (‖x‖ / 5 - 1) *
        (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))))) 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    hmem.const_mul C
  exact hmemC.mono' hf (Filter.Eventually.of_forall h)

end Commons.Measure.EuclideanSpace
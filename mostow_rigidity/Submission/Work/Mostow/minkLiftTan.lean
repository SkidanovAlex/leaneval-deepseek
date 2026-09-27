import Mathlib
import Submission.Work.Mostow.localIsomDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The sum of squares of the coordinates of a chart point is its squared norm. -/
theorem sum_sq_eq_norm_sq {n : ℕ} (v : E n) : (∑ i : Fin n, v i * v i) = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq v, PiLp.inner_apply]
  simp [pow_two]

/-- The Minkowski square of the tangent lift `liftTan p v` is the hyperbolic metric `gH p v`. -/
theorem minkLiftTan {n : ℕ} (p v : E n) : mink_localIsomDefs (liftTan p v) (liftTan p v) = gH p v := by
  have hsum : (∑ i : Fin n, v i * v i) = ‖v‖ ^ 2 := sum_sq_eq_norm_sq v
  rw [mink_localIsomDefs, liftTan, gH]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hsum, ← tpart_sq p]
  field_simp

end Work.Mostow

import Submission.Mostow.SubHypDefs

/-!
# Lead-written vocabulary for geodesic strata (k = 1 case of GAP-A); definitions only, DO NOT EDIT
-/

open LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Submission.Mostow

noncomputable section

/-- exact Euclidean coordinates about the standard stratum: normal coordinate `W` is the chart's normal part -/
def fermiW (k m : ℕ) (v : E k) (W : E m) : E (k + m) :=
  WithLp.toLp 2 (Fin.append (fun i => √(1 + ‖W‖ ^ 2) * v i) (fun i => W i))

/-- operator-norm distance of a linear isometry from the identity -/
def rotN {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m) : ℝ :=
  ‖(R.toLinearIsometry.toContinuousLinearMap : E m →L[ℝ] E m) - ContinuousLinearMap.id ℝ (E m)‖

end

end Submission.Mostow

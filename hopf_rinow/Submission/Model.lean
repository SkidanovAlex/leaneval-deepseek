import Mathlib
import Submission.CLMInstances

/-!
# Model-space geodesic theory (in progress)

For a finite-dimensional normed space `E` over `ℝ` and a smooth family
`g : E → E →L[ℝ] E →L[ℝ] ℝ` of symmetric positive-definite bilinear forms
(a "chart metric"), geodesics are solutions of the second-order
Euler–Lagrange ODE of the energy `L(x,v) = ½ g(x)(v,v)`:

  `g(c)(v', w) = ½ (Dg(c)(w))(v,v) − (Dg(c)(v))(v,w)`   for all `w`,
-/

open ContinuousLinearMap
open Set
open scoped ContDiff

namespace Submission.Model

open Submission.CLMInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Bilin (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ

/-- Evaluation `u ↦ (u v) v` of a bilinear map at the pair `(v,v)`. -/
noncomputable def evalAtV (v : E) : Bilin E →L[ℝ] ℝ := by
  let e1 : Bilin E →L[ℝ] (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := E →L[ℝ] ℝ) v
  let e2 : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := ℝ) v
  exact e2.comp e1

/-- The right hand side covector of the Euler–Lagrange equations,
`w ↦ ½ (T w)(v,v) − (T v)(v,w)`, where `T : E →L Bilin E` stands for `Dg(x)`. -/
noncomputable def rhsCovector (T : E →L[ℝ] Bilin E) (v : E) : E →L[ℝ] ℝ := by
  let cv1 : E →L[ℝ] ℝ := (evalAtV v).comp T
  let cv2 : E →L[ℝ] ℝ := (T v) v
  exact (1 / 2 : ℝ) • cv1 - cv2

/-- The acceleration term `a(x, v) := -♯(x)(R(x,v))`, given the flat map `gx : Bilin E`
(assumed invertible) and the derivative `T = Dg(x)`. -/
noncomputable def accel (gx : Bilin E) (T : E →L[ℝ] Bilin E) (v : E) : E :=
  (ContinuousLinearMap.inverse gx) (rhsCovector T v)



section ODE

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The first-order system for the geodesic equation: `(x, v) ↦ (v, a(x,v))`. -/
noncomputable def odeField (g : E → Bilin E) : E × E → E × E := fun z =>
  (z.2, accel (g z.1) (fderiv ℝ g z.1) z.2)

end ODE

end Submission.Model

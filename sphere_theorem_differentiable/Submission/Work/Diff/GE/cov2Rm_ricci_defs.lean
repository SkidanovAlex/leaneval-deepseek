import Mathlib
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.GE.kato_covRm_field
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions and bookkeeping for the Ricci identity of `∇²Rm`

Glue module for `Work.Diff.GE.cov2Rm_ricci`.  The second covariant derivative of the curvature
`Work.Diff.GE.cov2Rm` is defined through `cov2RmExt`; the general abstract identity for the second
covariant derivative of a field-level tensor is `Work.Diff.GE.extDD_antisymm`.  To apply it to the
curvature we need the curvature `(0,4)`-tensor as an `ExtTensor` of arity `4`, together with its
smoothness and its real-linearity in each slot.

Everything here is bookkeeping about `Submission.Diff.rmP`; the only inputs are the already proved
`Work.Diff.GE.rmP_fields_smooth` and the pointwise multilinearity lemmas `rmP_add_*`, `rmP_smul_*`
of `Submission.Work.Diff.GE.NablaRm`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The curvature `(0,4)`-tensor of `g`, `rmP g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)`, as a
field-level tensor of arity `Fin 4`. -/
noncomputable abbrev rmPTensor (g : SMet I M) : ExtTensor (I := I) (M := M) (Fin 4) :=
  fun F y => rmP g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)

/-- The tuple of four fields `(A, B, C, D)`, as an element of `Fin 4 → fields`. -/
abbrev rmPQuad (A B C D : Π y : M, TangentSpace I y) : Fin 4 → (Π y : M, TangentSpace I y) :=
  ![A, B, C, D]

/-- Pointwise unfolding of `rmPTensor`. -/
@[simp] theorem rmPTensor_apply (g : SMet I M) (F : Fin 4 → (Π y : M, TangentSpace I y)) (y : M) :
    rmPTensor g F y = rmP g y (F 0 y) (F 1 y) (F 2 y) (F 3 y) := rfl

@[simp] theorem rmPQuad_zero (A B C D : Π y : M, TangentSpace I y) :
    rmPQuad A B C D 0 = A := rfl

@[simp] theorem rmPQuad_one (A B C D : Π y : M, TangentSpace I y) :
    rmPQuad A B C D 1 = B := rfl

@[simp] theorem rmPQuad_two (A B C D : Π y : M, TangentSpace I y) :
    rmPQuad A B C D 2 = C := rfl

@[simp] theorem rmPQuad_three (A B C D : Π y : M, TangentSpace I y) :
    rmPQuad A B C D 3 = D := rfl

/-- `rmPTensor g` is smooth on smooth tuples. -/
theorem rmPTensor_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {F : Fin 4 → (Π y : M, TangentSpace I y)} (hF : SmoothTuple F) :
    SmoothFunT (I := I) (M := M) (rmPTensor g F) :=
  rmP_fields_smooth (I := I) (M := M) hLC g (hF 0) (hF 1) (hF 2) (hF 3)

/-- `rmPTensor g` is additive in each of its four slots (as a function on `M`). -/
theorem rmPTensor_add (hLC : LCSmooth I M) (g : SMet I M)
    (F : Fin 4 → (Π y : M, TangentSpace I y)) (i : Fin 4)
    (G H : Π y : M, TangentSpace I y) :
    rmPTensor g (Function.update F i (G + H))
      = rmPTensor g (Function.update F i G) + rmPTensor g (Function.update F i H) := by
  funext y
  fin_cases i <;> simp only [rmPTensor, Function.update_apply, Pi.add_apply, Fin.isValue]
  · exact rmP_add_fst g hLC y _ _ _ _ _
  · exact rmP_add_snd g hLC y _ _ _ _ _
  · exact rmP_add_thd g hLC y _ _ _ _ _
  · exact rmP_add_fth g hLC y _ _ _ _ _

/-- `rmPTensor g` is `ℝ`-homogeneous in each of its four slots (as a function on `M`). -/
theorem rmPTensor_smul (hLC : LCSmooth I M) (g : SMet I M)
    (F : Fin 4 → (Π y : M, TangentSpace I y)) (i : Fin 4)
    (G : Π y : M, TangentSpace I y) (c : ℝ) :
    rmPTensor g (Function.update F i (c • G)) = c • rmPTensor g (Function.update F i G) := by
  funext y
  fin_cases i <;> simp only [rmPTensor, Function.update_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue]
  · exact rmP_smul_fst g hLC y _ _ _ _ _
  · exact rmP_smul_snd g hLC y _ _ _ _ _
  · exact rmP_smul_thd g hLC y _ _ _ _ _
  · exact rmP_smul_fth g hLC y _ _ _ _ _

end Work.Diff.GE

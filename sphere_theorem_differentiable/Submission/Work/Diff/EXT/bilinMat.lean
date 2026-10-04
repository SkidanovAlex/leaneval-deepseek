/-
# Bilinear forms on the model space of a chart, from their matrices

For an `ℝ`-normed space `E` (finite dimensional and complete) with the canonical basis `bB`, this
file provides the **linear reconstruction of a bilinear form from its matrix**:

`matToBilin : MatE →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)`,

characterised by `matToBilin M (bB i) (bB j) = M i j` (`matToBilin_apply_basis`).  Together with
`eq_of_apply_basis_basis` (two continuous bilinear forms agreeing on all basis pairs are equal)
this is the tool that converts *matrix valued* smoothness data (the chart matrix `chartMat` of a
metric family) into *continuous-linear-map valued* smoothness data (the metric as a section of the
bundle of bilinear forms), which is what `Work.Diff.EXT.contMDiffAt_section_of_chartMat` needs.

The only subtlety of the construction is type-class inference: `E →L[ℝ] E →L[ℝ] ℝ` is a
continuous-linear-map space, and synthesising its algebraic structure at default heartbeats is
expensive, so this file raises `synthInstance.maxHeartbeats`.  (The option is file-local: an
importing file that needs the same instances should set it again.)
-/

import Mathlib
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]

/-- The `i`-th coordinate functional of the canonical basis `bB`, as a continuous linear
functional. -/
noncomputable def bCoordCLM (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((bB (E := E)).coord i)

/-- The elementary bilinear form `(u, v) ↦ (bB.coord i) u * (bB.coord j) v`. -/
noncomputable def bilinElem (i j : Fin (Module.finrank ℝ E)) : E →L[ℝ] E →L[ℝ] ℝ :=
  (bCoordCLM (E := E) i).smulRight (bCoordCLM (E := E) j)

/-- The `(i,j)`-th matrix entry, as a continuous linear functional on `MatE`. -/
noncomputable def matEntryCLM (i j : Fin (Module.finrank ℝ E)) : MatE (E := E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj (φ := fun _ : Fin (Module.finrank ℝ E) => ℝ) j).comp
      (LinearMap.proj (φ := fun _ : Fin (Module.finrank ℝ E) =>
        (Fin (Module.finrank ℝ E) → ℝ)) i))

/-- **Linear reconstruction of a bilinear form from its matrix in the basis `bB`.** -/
noncomputable def matToBilinLin : MatE (E := E) →ₗ[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (matEntryCLM (E := E) i j).smulRight (bilinElem (E := E) i j)

/-- **Reconstruction of a bilinear form from its matrix in the basis `bB`.**  The bilinear form
`matToBilin M` is the continuous linear map `E →L[ℝ] E →L[ℝ] ℝ` whose matrix in the basis `bB` is
`M`, i.e. `matToBilin M (bB i) (bB j) = M i j` (`matToBilin_apply_basis`). -/
noncomputable def matToBilin : MatE (E := E) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (F' := E →L[ℝ] E →L[ℝ] ℝ) matToBilinLin

/-- The defining property of `matToBilin`: it has the prescribed matrix in the basis `bB`. -/
theorem matToBilin_apply_basis (M : MatE (E := E)) (i j : Fin (Module.finrank ℝ E)) :
    matToBilin M (bB (E := E) i) (bB (E := E) j) = M i j := by
  rw [show matToBilin M = matToBilinLin M from rfl]
  simp only [matToBilinLin, matEntryCLM, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, bilinElem, ContinuousLinearMap.smulRight_apply, bCoordCLM,
    LinearMap.coe_toContinuousLinearMap]
  simp
  simp only [Finsupp.single_apply]
  simp

/-- Two continuous linear maps out of `E` that agree on the basis `bB` are equal. -/
lemma clm_ext_basis {M' : Type*} [NormedAddCommGroup M'] [NormedSpace ℝ M']
    {F G : E →L[ℝ] M'} (h : ∀ i, F (bB (E := E) i) = G (bB (E := E) i)) : F = G := by
  have h' : F.toLinearMap = G.toLinearMap := Module.Basis.ext (bB (E := E)) h
  exact ContinuousLinearMap.ext fun w => DFunLike.congr_fun h' w

/-- Two continuous bilinear forms on `E` that agree on the pairs `(bB i, bB j)` are equal. -/
theorem eq_of_apply_basis_basis {F G : E →L[ℝ] E →L[ℝ] ℝ}
    (h : ∀ i j, F (bB (E := E) i) (bB (E := E) j) = G (bB (E := E) i) (bB (E := E) j)) :
    F = G :=
  clm_ext_basis fun i => clm_ext_basis fun j => h i j

end Work.Diff.EXT

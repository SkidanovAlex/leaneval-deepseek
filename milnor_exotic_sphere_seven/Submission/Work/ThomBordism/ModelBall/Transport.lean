import Mathlib
import Submission.Work.PTGeometric.exists_chartedSpace_and_isManifold_of_homeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Transporting a charted space / manifold structure across a homeomorphism

Two lemmas generalising `Work.PTGeometric.exists_chartedSpace_and_isManifold_of_homeomorph` (which is
stated at dimension `9`): the charted space structure `Work.PTGeometric.pushedChartedSpace e`
obtained by pushing forward the atlas of `X` along a homeomorphism `e : X ≃ₜ Y` is a `C^n` manifold
whenever `X` is, and its boundary is the preimage of the boundary of `X` under `e` (i.e. a point `y`
is a boundary point of `Y` exactly when `e.symm y` is a boundary point of `X`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Topology Manifold

namespace Work.ThomBordism

noncomputable section

/-- **The boundary of a pushed charted space.**  If the charted space structure of `Y` is obtained
by pushing forward the atlas of `X` along `e : X ≃ₜ Y`, then `y ∈ ∂Y ↔ e.symm y ∈ ∂X`. -/
theorem mem_boundary_pushedChartedSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace H X] (e : X ≃ₜ Y) (y : Y) :
    letI : ChartedSpace H Y := Work.PTGeometric.pushedChartedSpace e
    (y ∈ I.boundary Y ↔ e.symm y ∈ I.boundary X) := by
  letI : ChartedSpace H Y := Work.PTGeometric.pushedChartedSpace e
  have hchart : (chartAt H y) y = (chartAt H (e.symm y)) (e.symm y) := rfl
  show I.IsBoundaryPoint y ↔ I.IsBoundaryPoint (e.symm y)
  rw [ModelWithCorners.isBoundaryPoint_iff, ModelWithCorners.isBoundaryPoint_iff]
  simp only [extChartAt_coe, Function.comp_apply, hchart]

/-- **The pushed charted space is a `C^n` manifold.** -/
theorem isManifold_pushedChartedSpace {X : Type*} [TopologicalSpace X] {Y : Type*}
    [TopologicalSpace Y] {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (e : X ≃ₜ Y)
    [ChartedSpace H X] [IsManifold I n X] :
    letI : ChartedSpace H Y := Work.PTGeometric.pushedChartedSpace e
    IsManifold I n Y := by
  letI : ChartedSpace H Y := Work.PTGeometric.pushedChartedSpace e
  haveI : HasGroupoid Y (contDiffGroupoid n I) :=
    Work.PTGeometric.hasGroupoid_pushedChartedSpace e (contDiffGroupoid n I)
  exact IsManifold.mk' I n Y

end

end Work.ThomBordism

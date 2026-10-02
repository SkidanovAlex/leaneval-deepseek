import Submission.Work.SphHomology.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The trivialised piece of the sphere bundle is charted

For a Euclidean bundle `Z` of rank `k ≥ 1` over a base charted on `ℝ⁸`, the model space
`↥(Z.baseSet i) × S^{k-1}` of the piece of the sphere bundle over a trivialising set is a charted
space modelled on `ℝ^{8 + (k-1)}`: an open piece of an `8`-manifold times the `(k-1)`-sphere,
with the model identification `ℝ^{8+(k-1)} ≅ ℝ⁸ × ℝ^{k-1}`.
-/

open scoped Topology Manifold
open Work.TangentClasses

namespace Work.SphHomology

noncomputable section

theorem sphPiece_charted_prod {B : Type*} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {k : ℕ} (hk : 1 ≤ k) {ι : Type*}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (i : ι) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin (8 + (k - 1))))
      (↥(Z.baseSet i) × ModelSph (EuclideanSpace ℝ (Fin k)))) := by
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin 8)) ↥(Z.baseSet i) :=
    TopologicalSpace.Opens.instChartedSpace ⟨Z.baseSet i, Z.isOpen_baseSet i⟩
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace, Fintype.card_fin]; omega⟩
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (ModelSph (EuclideanSpace ℝ (Fin k))) :=
    EuclideanSpace.instChartedSpaceSphere
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin (k - 1)))
      (↥(Z.baseSet i) × ModelSph (EuclideanSpace ℝ (Fin k))) :=
    prodChartedSpace _ _ _ _
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + (k - 1))))
      (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin (k - 1))) :=
    Homeomorph.chartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 8) (m := k - 1)).toHomeomorph
  refine ⟨ChartedSpace.comp (EuclideanSpace ℝ (Fin (8 + (k - 1))))
    (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin (k - 1)))
    (↥(Z.baseSet i) × ModelSph (EuclideanSpace ℝ (Fin k)))⟩

end

end Work.SphHomology

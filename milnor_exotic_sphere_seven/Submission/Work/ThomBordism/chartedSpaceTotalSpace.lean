import Mathlib
import Submission.Work.SphHomology.PieceCharted
import Submission.Work.SphHomology.sphPiece_homeo
import Submission.Work.Topology.VectorBundleCoreTotalSpaceLocallyCompact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The total space of a real bundle over an `8`-manifold is charted on `ℝ^{8+k}`

A real bundle `Z` over a topological space `B` is (by definition of `RealBundle`) a gluing datum
`VectorBundleCore ℝ B F ι`.  Mathlib's `FiberBundle.chartedSpace` realises the total space of such
a bundle as a charted space modelled on the product of a model of the base with the fibre, and
`EuclideanSpace.finAddEquivProd` identifies `ℝ⁸ × ℝᵏ` with `ℝ^{8+k}`.  Consequently the total space
of a rank-`k` real bundle over a base charted on `ℝ⁸` is a charted space modelled on
`EuclideanSpace ℝ (Fin (8 + k))`.
-/

namespace Work.ThomBordism

/-- **The total space of a real bundle over an `8`-manifold is a charted space** modelled on
`EuclideanSpace ℝ (Fin (8 + k))`. -/
theorem chartedSpaceTotalSpace {B : Type} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {ι : Type} {k : ℕ} (hk : 1 ≤ k)
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin (8 + k))) Z.TotalSpace) := by
  letI := Z.fiberBundle
  -- The bundle is a fibre bundle with fibre `ℝ^k`, so its total space is charted on `ℝ⁸ × ℝ^k`.
  haveI : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 8)) (EuclideanSpace ℝ (Fin k)))
      Z.TotalSpace :=
    FiberBundle.chartedSpace
  -- `ℝ⁸ × ℝ^k` is `ℝ^{8+k}`.
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + k)))
      (ModelProd (EuclideanSpace ℝ (Fin 8)) (EuclideanSpace ℝ (Fin k))) :=
    Homeomorph.chartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 8) (m := k)).toHomeomorph
  exact ⟨ChartedSpace.comp (EuclideanSpace ℝ (Fin (8 + k)))
    (ModelProd (EuclideanSpace ℝ (Fin 8)) (EuclideanSpace ℝ (Fin k))) Z.TotalSpace⟩

end Work.ThomBordism

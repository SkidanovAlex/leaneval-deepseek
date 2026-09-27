import Mathlib
import Submission.Work.Drive.chartedSpaceChangeModel
import Submission.Work.Drive.exists_cappingModel_projectivization

/-!
# The capping space as a smooth `4`-manifold, with transparent charts

`Submission/Work/Drive/exists_chartedSpace_isManifold_cappingSpace` proves that the capping space
`Y = Work.Drive.CappingSpace` of Hugelmeyer's fifth auxiliary result carries *some* smooth
`4`-manifold structure modelled on `ℝ⁴ = EuclideanSpace ℝ (Fin 4)`, but as an `∃`, so its charts are
opaque and no smoothness statement about a concrete map into `Y` can be reduced to them.

This file gives the structure by *transporting, along the concrete homeomorphism*

* `Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³`

(of `Submission/Work/Drive/exists_cappingModel_projectivization`), the transparent structure

* `Work.Drive.halfLineProjectiveCharted : ChartedSpace ℝ⁴ ((0,∞) × ℝP³)`

(of `Submission/Work/Drive/chartedSpaceChangeModel`), whose charts are built from the projective
charts `Work.Drive.projChart` of `ℝP³` (via `Work.Drive.projCharted`), the exponential chart of
`(0,∞)`, and the model change along the linear homeomorphism `ℝ¹ × ℝ³ ≃ₜ ℝ⁴`.

Consequently smoothness of a map into `CappingSpace` can be reduced, by
`Work.Drive.chartedStructure_contMDiffWithinAt` (transport along a homeomorphism) and
`Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel` (model change), to smoothness of the explicit
composite with `cappingSpaceHomeoProj`, and then to the concrete projective coordinates
`Work.Drive.projChartMap`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The transparent smooth structure on the capping space**, obtained by transporting
`Work.Drive.halfLineProjectiveCharted` along the concrete homeomorphism
`Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³`. -/
def cappingCharted : ChartedSpace (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  exact Homeomorph.chartedSpace cappingSpaceHomeoProj.symm

/-- **The capping space is a smooth `4`-manifold for the transparent structure `cappingCharted`.** -/
theorem isManifold_cappingCharted :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 4)) _ _ (EuclideanSpace ℝ (Fin 4)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      Work.Drive.CappingSpace _ cappingCharted := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  haveI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    isManifold_halfLineProjectiveCharted
  exact homeomorph_isManifold cappingSpaceHomeoProj.symm
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))

end

end Work.Drive

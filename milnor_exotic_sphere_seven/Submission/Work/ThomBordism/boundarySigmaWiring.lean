import Submission.Work.ThomBordism.boundaryDualityExplicit
import Submission.Work.ThomBordism.boundaryFinite
import Submission.Work.ThomBordism.boundaryNondegenerate
import Submission.Work.ThomBordism.boundaryHalfDimension

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.BoundarySigma`: the one-line wiring of the chain

`Work.ThomBordism.boundarySigma_of_explicit` (`boundaryDualityExplicit.lean`) reduces
`Work.ThomBordism.BoundarySigma` — hence the area's target `Work.Drive.ThomRational`, through
`Work.ThomBordism.thomRational_of_inputs` — to the three fields of
`Work.ThomBordism.BoundaryDualityExplicit`:

* `BoundaryFinite` = `Work.ThomBordism.boundaryFinite` (finiteness of `H⁴(∂W;ℚ)`, from the pieces
  along `W.bdry`), **proved**;
* `BoundaryNondegenerate` = `Work.ThomBordism.boundaryNondegenerate` (middle-degree Poincaré
  duality of the closed `8`-manifold `∂W`), **proved**;
* `BoundaryHalfDimension` = `Work.ThomBordism.boundaryHalfDimension` (middle-degree Lefschetz
  duality for the pair `(W, ∂W)`), which is the crux
  `Work.ThomBordism.BoundaryMaximalIsotropic`; see `DETECTION_STATUS.md` for the two remaining gaps
  on its routes (`Work.ThomBordism.Detection` and the collar behind
  `Work.ThomBordism.LefschetzDualityBdry`).

The theorem below is the assembly; it is a *proved* reduction (no `sorry` of its own) and is what the
target file consumes once `boundaryHalfDimension` is sorry-free.
-/

set_option autoImplicit false

namespace Work.ThomBordism

/-- **`BoundarySigma` from the crux alone**, the other two inputs being the proved
`boundaryFinite` and `boundaryNondegenerate`. -/
theorem boundarySigma_of_halfDimension (hhalf : BoundaryHalfDimension) : BoundarySigma :=
  boundarySigma_of_explicit
    { finite := boundaryFinite
      nondegenerate := boundaryNondegenerate
      halfDimension := hhalf }

/-- The same, with the crux `Work.ThomBordism.BoundaryMaximalIsotropic` as the input. -/
theorem boundarySigma_of_maximalIsotropic (hmax : BoundaryMaximalIsotropic) : BoundarySigma :=
  boundarySigma_of_halfDimension (boundaryHalfDimension_of_maximalIsotropic hmax)

end Work.ThomBordism

import Submission.Work.PTGeometric.TubeAmbient
import Submission.Work.PTGeometric.trace_starProjection
import Submission.Work.PTGeometric.RieszProj.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the tube's ambient projection is a rank-`k` orthogonal projection

`Work.PTGeometric.tubeNormalProj` is the orthogonal projection onto the normal space at the foot of a
point of a tube chart, and `Work.PTGeometric.TubeAmbient` proves that it is `C^∞` on the open tube.
For the last mile (`Work.PTGeometric.AmbientCollapseEnd.isProj`) the projection must moreover be a
point of the Grassmannian `Work.PTGeometric.Gr (8+k) k` of rank-`k` orthogonal projections, i.e. be
self-adjoint, idempotent and of trace `k`.  This file supplies those three properties:

* self-adjointness and idempotence come from Mathlib's `Submodule.starProjection`
  (`Submodule.adjoint_subtypeL`, `Submodule.adjoint_orthogonalProjectionOnto`,
  `ContinuousLinearMap.adjoint_comp`, `Submodule.isIdempotentElem_starProjection`),
* the trace is `Work.PTGeometric.trace_starProjection` (the trace of an orthogonal projection is the
  dimension of its range) together with `Work.Tubular.finrank_normalSpace` (`dim ν_x = k`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

variable {V : Work.ThomBordism.Man8} {k : ℕ} {ε : ℝ}

/-- **The tube's ambient projection is a rank-`k` orthogonal projection.** -/
theorem tubeNormalProj_mem_Gr (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (C : Work.Tubular.TubeChart E ε) (y : Work.Tubular.Euc (8 + k)) :
    tubeNormalProj E C y ∈ Gr (8 + k) k := by
  have hP : tubeNormalProj E C y
      = (Work.Tubular.normalSpace E (tubeFoot E C y)).starProjection := rfl
  rw [hP]
  refine ⟨?_, ?_, ?_⟩
  · show ContinuousLinearMap.adjoint
        ((Work.Tubular.normalSpace E (tubeFoot E C y)).subtypeL.comp
          ((Work.Tubular.normalSpace E (tubeFoot E C y)).orthogonalProjectionOnto))
      = (Work.Tubular.normalSpace E (tubeFoot E C y)).subtypeL.comp
          ((Work.Tubular.normalSpace E (tubeFoot E C y)).orthogonalProjectionOnto)
    rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_orthogonalProjectionOnto,
      Submodule.adjoint_subtypeL]
  · exact Submodule.isIdempotentElem_starProjection (Work.Tubular.normalSpace E (tubeFoot E C y))
  · show LinearMap.trace ℝ (Work.Tubular.Euc (8 + k))
      (((Work.Tubular.normalSpace E (tubeFoot E C y)).subtypeL).comp
        ((Work.Tubular.normalSpace E (tubeFoot E C y)).orthogonalProjectionOnto)) = (k : ℝ)
    rw [trace_starProjection, Work.Tubular.finrank_normalSpace]
    norm_num

end

end Work.PTGeometric

import Submission.Work.Tubular.exists_halfSpaceHomeo_boundary
import Submission.Work.Tubular.exists_normalDiscManifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The named disc-bundle atlas at the `n + 1` model convention

`Work.Surgery.HasCollar (n) (M)` and `Work.Orient.Boundary.RelativeFundamentalClassExists (n)` are
phrased for the model `EuclideanHalfSpace (n + 1)`, while `Work.Tubular.NormalDiscManifold` (and
`Work.Tubular.mem_boundary_normalDiscSub`) live at `EuclideanHalfSpace (8 + k)`.  The two indices
`7 + k + 1` and `8 + k` are only propositionally equal, so the charted structure has to be
*transported* — and, because the collar and the ORIENT theorem need to know where the boundary is,
the transport must be a **named** term (a `def`, usable in a `letI`), not a `Classical.choice` of a
`Nonempty` (see README §33.6).

This module provides the named transport:
* `Work.Tubular.halfSpaceHomeo k` — the relabelling homeomorphism
  `EuclideanHalfSpace (7 + k + 1) ≃ₜ EuclideanHalfSpace (8 + k)`, chosen from the proved
  `Work.Tubular.exists_halfSpaceHomeo_boundary` so that its boundary preservation is *recorded*
  (`Work.Tubular.halfSpaceHomeo_boundary`);
* `Work.Tubular.chartedSpace_normalDisc_add C R` — the composite of the canonical disc-bundle atlas
  `chartedSpaceOfModelHomeo (discChartedSpace C) R.Λ` with that relabelling, as a `def`.
-/

open scoped Manifold Topology
open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-- **The relabelling homeomorphism of the two half-space models**
`EuclideanHalfSpace (7 + k + 1) ≃ₜ EuclideanHalfSpace (8 + k)`. -/
noncomputable def halfSpaceHomeo (k : ℕ) :
    EuclideanHalfSpace (7 + k + 1) ≃ₜ EuclideanHalfSpace (8 + k) :=
  Classical.choose (exists_halfSpaceHomeo_boundary k)

/-- **The defining property of `Work.Tubular.halfSpaceHomeo`**: it preserves the boundary
hyperplane. -/
theorem halfSpaceHomeo_boundary (k : ℕ) (x : EuclideanHalfSpace (7 + k + 1)) :
    (halfSpaceHomeo k x).val 0 = 0 ↔ x.val 0 = 0 :=
  Classical.choose_spec (exists_halfSpaceHomeo_boundary k) x

/-- **The named disc-bundle atlas in the `n + 1` convention**: the canonical atlas
`chartedSpaceOfModelHomeo (discChartedSpace C) R.Λ` reindexed by the relabelling `halfSpaceHomeo`. -/
noncomputable def chartedSpace_normalDisc_add {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (R : DiscManifold.HalfModelReindex k) :
    ChartedSpace (EuclideanHalfSpace (7 + k + 1)) (NormalDiscSub E ε) :=
  chartedSpaceOfModelHomeo (chartedSpaceOfModelHomeo (discChartedSpace C) R.Λ) (halfSpaceHomeo k)

end

end Work.Tubular

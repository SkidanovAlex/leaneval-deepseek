import Submission.Work.Surgery.bnd_isManifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The boundary manifold: instances

`Submission/Work/Surgery/bnd_isManifold.lean` (delegated) proves that for a `C^∞` manifold `M`
with boundary, modelled on the half-space `EuclideanHalfSpace (n+1)`, the boundary
`∂M = (𝓡∂ (n+1)).boundary M`, with the preferred atlas `boundaryChartedSpace`, is a smooth
`n`-manifold modelled on the boundaryless model `𝓡 n`.

This file registers those structures as global instances, so that from now on `∂M` can be used as a
manifold with no further setup, and records the elementary part of their functoriality (the
inclusion `bndIncl`, its continuity).

The smoothness of `bndIncl` and the restriction of diffeomorphisms to the boundary live in
`Submission/Work/Surgery/bnd_incl_contMDiff.lean` and
`Submission/Work/Surgery/bnd_diffeomorph.lean` (delegated), and are re-exported by
`Submission/Work/Surgery/BoundaryManifold.lean`.
-/

open scoped Manifold Topology ContDiff
open Function

namespace Work.Surgery

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) (∞ : WithTop ℕ∞) M]

/-- The preferred charted-space structure on the boundary of a manifold with boundary, as an
instance. -/
@[instance_reducible]
noncomputable instance bndChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M) :=
  boundaryChartedSpace (n := n) (M := M)

/-- The smooth manifold structure on the boundary of a manifold with boundary, as an instance. -/
instance bndIsManifold : IsManifold (𝓡 n) (∞ : WithTop ℕ∞) ((𝓡∂ (n + 1)).boundary M) :=
  bnd_isManifold n

/-- The boundary of an `(n+1)`-manifold with boundary is boundaryless (it is modelled on the
boundaryless model `𝓡 n`). -/
instance bndBoundaryless : BoundarylessManifold (𝓡 n) ((𝓡∂ (n + 1)).boundary M) :=
  inferInstance

/-- **The inclusion of the boundary**, as a map into `M`. -/
def bndIncl : ((𝓡∂ (n + 1)).boundary M) → M := fun p => p.1

@[simp] theorem bndIncl_apply (p : (𝓡∂ (n + 1)).boundary M) : bndIncl p = p.1 := rfl

theorem continuous_bndIncl : Continuous (bndIncl (n := n) (M := M)) := continuous_subtype_val

end

end Work.Surgery

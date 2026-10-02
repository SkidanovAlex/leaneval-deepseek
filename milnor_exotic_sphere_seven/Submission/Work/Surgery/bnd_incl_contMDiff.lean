import Mathlib
import Submission.Work.Surgery.BoundaryInstances

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The inclusion of the boundary of a manifold with boundary

`Submission/Work/Surgery/Boundary.lean` endows the boundary `∂M` of a `C^∞` `(n+1)`-manifold `M`
with boundary with the preferred atlas `boundaryChartedSpace` (charts obtained by restricting a
chart of `M` to the boundary and deleting the first coordinate), and
`Submission/Work/Surgery/bnd_isManifold.lean` shows that this makes `∂M` a smooth `n`-manifold.

This file proves **`Work.Surgery.bnd_incl_contMDiff`**: the inclusion `∂M → M` is smooth.

## The argument

By `contMDiff_iff` it suffices to check, for a boundary point `x` and an ambient point `y`, that
the local expression `z ↦ extChartAt 𝓡∂ y ((extChartAt 𝓡 n x).symm z).1` is `C^∞` on the relevant
set.  The model of `∂M` is the boundaryless model `𝓡 n = modelWithCornersSelf`, so the extended
chart of `∂M` at `x` is exactly the preferred boundary chart at `x` (it is the chart, followed by
the identity of the model space); this is the content of the elementary lemmas
`bndExtChartAt_apply`, `bndExtChartAt_source`, `bndExtChartAt_target`, `bndExtChartAt_symm`.  On
the relevant set the local expression is therefore

`z ↦ extChartAt 𝓡∂ y ((extChartAt 𝓡∂ x.1).symm (consZeroCLM n z))`,

the transition between two charts of the ambient manifold `M`, read through the linear map
`consZeroCLM n` that inserts a zero in the first coordinate — smooth by
`Work.Surgery.contDiffOn_extChartAt_comp_symm` (proved in `bnd_isManifold.lean`), composed with the
linear `consZeroCLM n`.  The `Set.MapsTo` that makes the composition legitimate is exactly the
statement that the chart of the boundary identifies `∂M` with the hyperplane `{z | z 0 = 0}`, read
in the charts of `M`.
-/

open scoped Manifold ContDiff Topology
open Function

namespace Work.Surgery

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The extended chart of the boundary in the boundaryless model

The boundary is modelled on `𝓡 n = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))`, whose
underlying map and its inverse are the identity.  Consequently the extended chart of `∂M` at `x`
(which is `chartAt` followed by the model) is the preferred boundary chart itself, on the nose:
same values, same source, same target, same inverse. -/

/-- The extended chart of the boundary at `x`, in the boundaryless model, has the same values as
the preferred boundary chart at `x`. -/
theorem bndExtChartAt_apply (x y : (𝓡∂ (n + 1)).boundary M) :
    (extChartAt (𝓡 n) x) y = boundaryChartAt x y := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe]
  simp

/-- The extended chart of the boundary at `x`, in the boundaryless model, has the same source as
the preferred boundary chart at `x`. -/
theorem bndExtChartAt_source (x : (𝓡∂ (n + 1)).boundary M) :
    (extChartAt (𝓡 n) x).source = (boundaryChartAt x).source := by
  rw [extChartAt_source]
  simp [boundaryChartedSpace_chartAt]

/-- The extended chart of the boundary at `x`, in the boundaryless model, has the same target as
the preferred boundary chart at `x`. -/
theorem bndExtChartAt_target (x : (𝓡∂ (n + 1)).boundary M) :
    (extChartAt (𝓡 n) x).target = (boundaryChartAt x).target := by
  rw [extChartAt_target]
  simp [boundaryChartedSpace_chartAt]

/-- The inverse of the extended chart of the boundary at `x`, in the boundaryless model, agrees
with the inverse of the preferred boundary chart at `x`. -/
theorem bndExtChartAt_symm (x : (𝓡∂ (n + 1)).boundary M) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ (extChartAt (𝓡 n) x).target) :
    (extChartAt (𝓡 n) x).symm z = (boundaryChartAt x).symm z := by
  have hz' : z ∈ (boundaryChartAt x).target := bndExtChartAt_target x ▸ hz
  refine (PartialEquiv.symm_apply_eq (extChartAt (𝓡 n) x) ?_ hz).mpr ?_
  · rw [bndExtChartAt_source]
    exact PartialEquiv.map_target _ hz'
  · rw [bndExtChartAt_apply]
    exact (OpenPartialHomeomorph.right_inv _ hz').symm

end

/-- **The inclusion of the boundary of a manifold with boundary is smooth.**  For a `C^∞`
`(n+1)`-manifold `M` with boundary, modelled on the half-space `EuclideanHalfSpace (n+1)`, the
inclusion `∂M → M` of the boundary (a smooth `n`-manifold, see `Work.Surgery.bnd_isManifold`) into
`M` is `C^∞`. -/
theorem bnd_incl_contMDiff (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M] :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M => p.1) := by
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, fun x y => ?_⟩
  have hG := contDiffOn_extChartAt_comp_symm (n := n) (M := M) x.1 y
  refine (hG.comp ((consZeroCLM n).contDiff.contDiffOn) (fun z hz => ?_)).congr
    (fun z hz => ?_)
  · -- the chart of the boundary lands in the charts of `M`: inserting a zero coordinate
    -- stays inside the target, and its inverse stays inside the source
    obtain ⟨hz1, hz2⟩ := hz
    have hz1' : z ∈ (boundaryChartAt x).target := bndExtChartAt_target x ▸ hz1
    have hz2' : ((extChartAt (𝓡 n) x).symm z).1 ∈
        (chartAt (EuclideanHalfSpace (n + 1)) y).source := by
      have h := hz2
      rw [Set.mem_preimage, extChartAt_source] at h
      exact h
    refine ⟨?_, ?_⟩
    · rw [boundaryChartAt_target x] at hz1'
      exact hz1'
    · rw [bndExtChartAt_symm x hz1, boundaryChartAt_symm x z hz1'] at hz2'
      exact hz2'
  · -- the local expression of the inclusion is the transition of the ambient charts,
    -- read through `consZeroCLM`
    obtain ⟨hz1, _⟩ := hz
    have hz1' : z ∈ (boundaryChartAt x).target := bndExtChartAt_target x ▸ hz1
    simp only [Function.comp_apply]
    rw [bndExtChartAt_symm x hz1, boundaryChartAt_symm x z hz1']

end Work.Surgery

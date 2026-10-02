import Mathlib
import Submission.Work.Tubular.chartedSpace_normalDisc_add
import Submission.Work.Tubular.mem_boundary_normalDiscSub

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

/-!
# The boundary of the disc bundle at the `n + 1` model convention

`Work.Tubular.mem_boundary_normalDiscSub` identifies the boundary of the normal disc bundle
`D_ε(ν)` with the sphere bundle `S_ε(ν)`, but for the charted space modelled on
`EuclideanHalfSpace (8 + k)` (`chartedSpaceOfModelHomeo (discChartedSpace C) R.Λ`).  Consumers such
as `Work.Surgery.HasCollar` read the same manifold at the model `EuclideanHalfSpace (7 + k + 1)`,
i.e. through the *named* atlas `Work.Tubular.chartedSpace_normalDisc_add C R`, which is the old
atlas transported along the relabelling homeomorphism `halfSpaceHomeo k`.

The boundary condition is a condition on the `0`-th coordinate of the extended chart, and
`Work.Tubular.halfSpaceHomeo_boundary` records that the relabelling preserves exactly this
coordinate.  Hence the boundary is unchanged by the transport, and the identification with the
sphere bundle `S_ε(ν)` (`normalNorm E p = ε`) carries over verbatim.

The transport statement is proved in the general form
`Work.Tubular.isBoundaryPoint_chartedSpaceOfModelHomeo_iff`: if a charted space is pushed along a
change of model `Φ : H ≃ₜ H'`, then a point is a boundary point for the new model `I` exactly when
it is one for the old model `I'`, provided `Φ` matches the two boundary hyperplanes
(here: `frontier (range I)` and `frontier (range I')`).

## Main results

* `Work.Tubular.isBoundaryPoint_chartedSpaceOfModelHomeo_iff` — boundary points are unchanged by
  pushing a charted space along a change of model that preserves the boundary hyperplane;
* `Work.Tubular.mem_boundary_normalDiscSub_add` — the boundary of `D_ε(ν)` in the `n + 1`
  convention is the sphere bundle.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Tubular

noncomputable section

/-- **Boundary points are unchanged by a change of model space.**

Let `c` be a charted space structure on `M` modelled on `H'`, and let `Φ : H ≃ₜ H'` be a
homeomorphism of model spaces.  Push `c` forward to the charted space
`chartedSpaceOfModelHomeo c Φ` modelled on `H`.  Then, for models with corners `I` on `H` and `I'`
on `H'` whose boundary hyperplanes correspond under `Φ`, a point of `M` is a boundary point for
`I` (in the pushed-forward structure) exactly when it is a boundary point for `I'` (in the original
structure).

The proof is the computation `extChartAt I p p = I (Φ.symm ((chartAt H' p) p))` of the extended
chart of the pushed-forward structure, together with the hypothesis on the boundary hyperplanes. -/
theorem isBoundaryPoint_chartedSpaceOfModelHomeo_iff {E E' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [c : ChartedSpace H' M] (Φ : H ≃ₜ H')
    (h : ∀ y : H', (I' y ∈ frontier (Set.range I') ↔ I (Φ.symm y) ∈ frontier (Set.range I)))
    (p : M) :
    letI : ChartedSpace H M := Work.Tubular.chartedSpaceOfModelHomeo c Φ
    (I.IsBoundaryPoint p ↔ I'.IsBoundaryPoint p) := by
  letI : ChartedSpace H M := Work.Tubular.chartedSpaceOfModelHomeo c Φ
  -- the chart of the pushed-forward structure is the old chart followed by `Φ.symm`
  have hch : (chartAt H p) p = Φ.symm ((chartAt H' p) p) := by
    show (OpenPartialHomeomorph.trans (chartAt H' p) Φ.symm.toOpenPartialHomeomorph) p
      = Φ.symm ((chartAt H' p) p)
    rw [OpenPartialHomeomorph.trans_apply]
    rfl
  show extChartAt I p p ∈ frontier (Set.range I) ↔ extChartAt I' p p ∈ frontier (Set.range I')
  rw [extChartAt_coe, extChartAt_coe]
  simp only [Function.comp_apply, hch]
  exact (h ((chartAt H' p) p)).symm

/-- **The boundary of the disc bundle in the `n + 1` model convention.**

`Work.Tubular.chartedSpace_normalDisc_add C R` is the atlas of `Work.Tubular.mem_boundary_normalDiscSub`
(the model `EuclideanHalfSpace (8 + k)`) transported along the relabelling of the coordinates
`halfSpaceHomeo k`.  Since that relabelling preserves the `0`-th coordinate, hence the boundary
hyperplane of the half-space model (`Work.Tubular.halfSpaceHomeo_boundary`), the boundary of the
disc bundle is the same set as before: the points whose normal vector has norm `ε`. -/
theorem mem_boundary_normalDiscSub_add {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (C : Work.Tubular.TubeChart E ε)
    (R : Work.Tubular.DiscManifold.HalfModelReindex k) (p : Work.Tubular.NormalDiscSub E ε) :
    letI : ChartedSpace (EuclideanHalfSpace (7 + k + 1)) (Work.Tubular.NormalDiscSub E ε) :=
      Work.Tubular.chartedSpace_normalDisc_add C R
    (p ∈ (modelWithCornersEuclideanHalfSpace (7 + k + 1)).boundary (Work.Tubular.NormalDiscSub E ε) ↔
      Work.Tubular.normalNorm E (p : Work.Tubular.NormalTotal E) = ε) := by
  -- the relabelling `halfSpaceHomeo k` matches the two boundary hyperplanes
  have hgeom : ∀ y : EuclideanHalfSpace (8 + k),
      (modelWithCornersEuclideanHalfSpace (8 + k)) y ∈ frontier
          (Set.range (modelWithCornersEuclideanHalfSpace (8 + k)))
        ↔ (modelWithCornersEuclideanHalfSpace (7 + k + 1))
            ((Work.Tubular.halfSpaceHomeo k).symm y) ∈ frontier
          (Set.range (modelWithCornersEuclideanHalfSpace (7 + k + 1))) := by
    intro y
    rw [frontier_range_modelWithCornersEuclideanHalfSpace (8 + k),
        frontier_range_modelWithCornersEuclideanHalfSpace (7 + k + 1)]
    simp only [Set.mem_ofPred_eq, modelWithCornersEuclideanHalfSpace_apply]
    have hb := Work.Tubular.halfSpaceHomeo_boundary k ((Work.Tubular.halfSpaceHomeo k).symm y)
    rw [Homeomorph.apply_symm_apply] at hb
    exact Iff.trans eq_comm (Iff.trans hb eq_comm)
  -- transport the boundary to the old model and use `mem_boundary_normalDiscSub`
  have hbridge := isBoundaryPoint_chartedSpaceOfModelHomeo_iff
      (I := modelWithCornersEuclideanHalfSpace (7 + k + 1))
      (I' := modelWithCornersEuclideanHalfSpace (8 + k))
      (c := Work.Tubular.chartedSpaceOfModelHomeo (Work.Tubular.discChartedSpace C) R.Λ)
      (Work.Tubular.halfSpaceHomeo k) hgeom p
  exact hbridge.trans (Work.Tubular.mem_boundary_normalDiscSub C R p)

end

end Work.Tubular

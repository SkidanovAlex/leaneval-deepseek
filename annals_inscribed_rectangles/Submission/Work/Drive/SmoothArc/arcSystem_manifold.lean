import Mathlib
import Submission.Work.Drive.hasLocalGraphCharts_regular_zeroSet_smooth
import Submission.Work.ManifoldParity.GraphInclusion
import Submission.Work.OneDim.arc_image_shape
import Submission.Work.OneDim.circle_gluing

/-!
# The `C^∞` `1`-manifold structure of a locally-graph set, and its parametrisations

The `C^∞` twin of `Submission/Work/Drive/arcSystem_manifold.lean` (which is stated at order `1`):
consequences of the *smooth* one-manifold classification (`Work.OneDim`) for sets `K ⊆ ℝ²` which are
locally the graph of a `C^∞` function over a coordinate axis (`Work.ManifoldParity.HasLocalGraphCharts`).
This is the assembly layer of the `C^∞` level-set arc chapter; the producer of the graph charts at
order `⊤` is `Work.Drive.SmoothGraph.hasLocalGraphCharts_regular_zeroSet`, and the *port recipe* for
the remaining files of the chapter is in `Submission/Work/Drive/SMOOTH_ARC_PORT.md`.
-/

namespace Work.Drive.SmoothArc

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

variable {K : Set (EuclideanSpace ℝ (Fin 2))}

/-- The inclusion of a locally-`C¹`-graph set into the plane, for the graph charted structure. -/
theorem contMDiff_subtype_val (hgra : Work.ManifoldParity.HasLocalGraphCharts K) :
    letI := Work.ManifoldParity.graphChartedSpace K hgra
    ContMDiff (modelWithCornersSelf ℝ Work.ManifoldParity.ME1) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      Work.OneDim.sm (Subtype.val : ↥K → EuclideanSpace ℝ (Fin 2)) :=
  Work.ManifoldParity.contMDiff_subtype_val_graph K hgra

/-- A `C¹` map into the locally-`C¹`-graph manifold `↥K`, followed by the inclusion, is a `C¹`
plane curve. -/
theorem contDiff_val_comp (hgra : Work.ManifoldParity.HasLocalGraphCharts K) {f : ℝ → ↥K} :
    letI := Work.ManifoldParity.graphChartedSpace K hgra
    ContMDiff (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 Work.OneDim.sm f →
      ContDiff ℝ Work.OneDim.sm (fun t : ℝ => (f t : EuclideanSpace ℝ (Fin 2))) := by
  letI := Work.ManifoldParity.graphChartedSpace K hgra
  intro hf
  have h := (contMDiff_subtype_val (K := K) hgra).comp hf
  rwa [contMDiff_iff_contDiff] at h

/-- **The classification alternative for an open connected subset** of a locally-`C¹`-graph set:
either the subset is parametrised bijectively by `ℝ` (an *arc*), or it is diffeomorphic to the
circle (a *loop*). -/
theorem exists_param_or_circle (hgra : Work.ManifoldParity.HasLocalGraphCharts K)
    (U : TopologicalSpace.Opens ↥K) [ConnectedSpace ↥U] :
    letI := Work.ManifoldParity.graphChartedSpace K hgra
    letI := Work.ManifoldParity.hasGroupoid_graph K hgra
    (∃ φ : ℝ → ↥U, Function.Bijective φ ∧
        IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 Work.OneDim.sm φ) ∨
      (Nonempty (Diffeomorph Work.OneDim.I1 Work.OneDim.I1 Circle ↥U Work.OneDim.sm)) := by
  letI := Work.ManifoldParity.graphChartedSpace K hgra
  letI := Work.ManifoldParity.hasGroupoid_graph K hgra
  haveI hism : IsManifold (modelWithCornersSelf ℝ Work.ManifoldParity.ME1) Work.OneDim.sm ↥K := IsManifold.mk' _ _ _
  haveI hgrU : HasGroupoid ↥U (contDiffGroupoid Work.OneDim.sm Work.OneDim.I1) := inferInstance
  haveI hismU : IsManifold Work.OneDim.I1 Work.OneDim.sm ↥U := IsManifold.mk' _ _ _
  let p : ↥U := Classical.arbitrary ↥U
  obtain ⟨s, γ, harc, hmax⟩ := Work.OneDim.exists_maximal_arc_param (C := ↥U) p
  rcases Work.OneDim.arc_image_shape (C := ↥U)
      (hend := fun γ hγ hinj x hx => Work.OneDim.end_behavior_injective hγ hinj hx) harc hmax with
    ⟨φ, hbij, hld⟩ | ⟨q, φ, hinj, hld, hrange, htop, hbot⟩
  · exact Or.inl ⟨φ, hbij, hld⟩
  · exact Or.inr (Work.OneDim.circle_gluing hinj hld hrange htop hbot)

end

end Work.Drive.SmoothArc

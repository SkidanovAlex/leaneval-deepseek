import Mathlib
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_levelSet_of_regular_tangent
import Submission.Work.Smooth.OneManifold.ae_isLocallyEuclidean_levelSet
import Submission.Work.Smooth.OneManifold.ae_niceLevel
import Submission.Work.BoxShrink.Pinch.PinchSweep

/-!
# Almost every box level is locally Euclidean and a union of circles — unconditionally

This file removes the vertex-genericity hypothesis `Work.Smooth.BoxGeneric.AeNoVertex` from the
results of `ae_isLocallyEuclidean_levelSet.lean`.  The vertex stratum is handled by the fourth local
model `Work.Smooth.OneManifold.isLocallyEuclideanAt_of_vertex_tangent`, and the required a.e.
statement — every vertex point of the surface is *tangential* — is
`Work.Smooth.BoxGeneric.AeVertex.aeVertexTangent`, which the box chapter proves **unconditionally**
(no genericity input, no classification input: it uses
`Work.Smooth.BoxGeneric.Vertex.vertexDir_mem_fderiv_range_of_not_isolated`).

Consequently:

* `Work.Smooth.OneManifold.ae_isLocallyEuclidean_levelSet_uncond`,
  `ae_isCircleUnion_levelSet_uncond` — for almost every `s`, the level set `F ∩ {boxNorm c σ = s}`
  is locally Euclidean of dimension one, hence a finite disjoint union of embedded circles;
* `Work.Smooth.OneManifold.aeTransverseBox_uncond` — almost every box sphere is transverse to the
  surface;
* `Work.Smooth.OneManifold.aeSlicedAll_of_jordanSchoenflies` (and the planar / classical-input
  variants) — the target `Work.BoxShrink.AeSlicedAll`, i.e. the field `ae` of
  `Work.BoxShrink.FinalInputS`, from the classical Jordan–Schoenflies theorem alone;
* `Work.Smooth.OneManifold.ae_niceLevel_uncond` — the corrected `BoxSliceNice`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **Almost every box level is locally Euclidean of dimension one** — no vertex genericity, no
classification input. -/
theorem ae_isLocallyEuclidean_levelSet_uncond (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsLocallyEuclidean (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  have hreg := Work.Smooth.BoxGeneric.FaceRegular.ae_face_regular_of_sardCoord
    (Work.Smooth.BoxGeneric.Sard.sardCoord ψ) c σ
  have hcorn := Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector (ψ := ψ) c σ
  have htan := Work.Smooth.BoxGeneric.aeVertexTangent ψ c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [hreg, hcorn, htan, hne] with s hs_reg hs_corn hs_tan hs_ne
  rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact Work.Smooth.BoxGeneric.BoxSphere_eq_empty_of_neg hslt c σ
    have hempty : Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s = ∅ := by
      rw [Work.Smooth.Morse.levelSet, hbox, Set.inter_empty]
    rw [hempty]
    intro x
    exact absurd x.2 (Set.notMem_empty _)
  · exact isLocallyEuclidean_levelSet_of_regular_tangent hsgt (fun i ε hε => hs_reg i ε hε)
      hs_corn hs_tan

/-- **Almost every box level is a finite disjoint union of circles** — unconditionally. -/
theorem ae_isCircleUnion_levelSet_uncond (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.IsCircleUnion ψ
        (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  have hloc := ae_isLocallyEuclidean_levelSet_uncond ψ c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  have hcont : Continuous (Submission.boxNorm c σ) :=
    Work.Topology.SphereSlicing.boxNorm_continuous c σ
  filter_upwards [hloc, hne] with s hsloc hsne
  rcases lt_or_gt_of_ne hsne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact Work.Smooth.BoxGeneric.BoxSphere_eq_empty_of_neg hslt c σ
    have hempty : Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s = ∅ := by
      rw [Work.Smooth.Morse.levelSet, hbox, Set.inter_empty]
    rw [hempty]
    exact isCircleUnion_empty ψ
  · exact isCircleUnion_of_isCompact_of_isLocallyEuclidean ψ
      (Work.Smooth.Morse.levelSet_subset_carrier ψ (Submission.boxNorm c σ) s)
      (Work.Smooth.Morse.Surface.isCompact_levelSet ψ hcont s) hsloc

/-- **Almost every box sphere meets the surface in general position** — unconditionally. -/
theorem aeTransverseBox_uncond (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Work.Smooth.BoxGeneric.AeTransverseBox ψ c σ := by
  have hcirc := ae_isCircleUnion_levelSet_uncond ψ c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [hcirc, hne] with s hcircs hsne
  rcases lt_or_gt_of_ne hsne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact Work.Smooth.BoxGeneric.BoxSphere_eq_empty_of_neg hslt c σ
    rw [hbox]
    exact Work.Smooth.BoxGeneric.transverseSphere_empty _
  · exact Work.Smooth.BoxGeneric.transverseSphere_of_isCircleUnion hcircs
      inter_subset_right (fun x hx => ⟨hx.2, hx.1⟩)

/-- **The target `Work.BoxShrink.AeSliced`, unconditionally modulo the classical slicing input.** -/
theorem aeSliced_of_sliceInput (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hS : Work.Topology.SphereSlicing.SliceInput (Work.Smooth.Morse.torus ψ)) :
    Work.BoxShrink.AeSliced ψ c σ :=
  Work.Smooth.BoxGeneric.aeSliced_of_aeTransverseBox ψ c σ (aeTransverseBox_uncond ψ c σ) hS

/-- **The target `Work.BoxShrink.AeSlicedAll` from the sphere-side Jordan–Schoenflies theorem
alone** — the `ae` field of `Work.BoxShrink.FinalInputS`. -/
theorem aeSlicedAll_of_jordanSchoenflies
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) :
    Work.BoxShrink.AeSlicedAll :=
  fun ψ c σ => aeSliced_of_sliceInput ψ c σ
    (Work.Smooth.BoxGeneric.sliceInput_of_jordanSchoenflies hjordan ψ)

/-- **The target `Work.BoxShrink.AeSlicedAll` from the *planar* Jordan–Schoenflies theorem
alone.** -/
theorem aeSlicedAll_of_planeHypothesis (hplane : Work.Smooth.SphereJordan.PlaneHypothesis) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_jordanSchoenflies (Work.Smooth.SphereJordan.jordanSchoenfliesSphere hplane)

/-- **The target `Work.BoxShrink.AeSlicedAll` from the classical slicing input on the standard
torus alone** (the form used by `Work.Smooth.BoxGeneric.aeSlicedAll_of_classicalInput`). -/
theorem aeSlicedAll_of_classicalInput
    (hCI : Work.Topology.SphereSlicing.ClassicalInput Work.CoreTopology.standard) :
    Work.BoxShrink.AeSlicedAll :=
  fun ψ c σ => aeSliced_of_sliceInput ψ c σ
    ((Work.Topology.SphereSlicing.sliceInput_map_homeomorph_iff ψ.toHomeomorph).mpr hCI.1)

/-- **Almost every box level is a nice level** — the corrected `BoxSliceNice`, unconditionally. -/
theorem ae_niceLevel_uncond (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.NiceLevel ψ (Work.BoxShrink.Pinch.boxLevel s c σ) 0 := by
  have hcirc := ae_isCircleUnion_levelSet_uncond ψ c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [hcirc, hne] with s hcircs _
  refine ⟨Work.Smooth.Morse.Surface.isCompact_levelSet ψ
      (Work.BoxShrink.Pinch.boxLevel_continuous s c σ) 0, ?_,
    Work.Smooth.Morse.Surface.isCompact_closedRegion ψ
      (Work.BoxShrink.Pinch.boxLevel_continuous s c σ) 0⟩
  rw [levelSet_boxLevel_eq ψ s c σ]
  exact hcircs

end

end Work.Smooth.OneManifold

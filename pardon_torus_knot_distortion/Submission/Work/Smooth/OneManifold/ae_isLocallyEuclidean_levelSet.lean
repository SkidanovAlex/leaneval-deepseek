import Mathlib
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_levelSet_of_regular
import Submission.Work.Smooth.OneManifold.Classify
import Submission.Work.Smooth.OneManifold.Consumer

/-!
# Almost every box level is locally Euclidean, and a finite union of circles

The chapter `Submission/Work/Smooth/BoxGeneric` proves that almost every box sphere meets the
surface `F = torus ψ` in a set which is *locally an arc*; here we upgrade the local model to the
local structure of a topological `1`-manifold:

* `ae_isLocallyEuclidean_levelSet`: for almost every level `s`, the level set
  `F ∩ {boxNorm c σ = s}` is locally Euclidean of dimension one;
* `ae_isCircleUnion_levelSet`: hence (by the classification of compact `1`-manifolds,
  `Work.Smooth.OneManifold.isCircleUnion_of_isCompact_of_isLocallyEuclidean`) it is a finite
  disjoint union of simple closed curves of `F`;
* `aeTransverseBox_of_vertex`: almost every box sphere meets `F` in general position, without any
  input beyond the genericity of the vertex stratum;
* `aeSlicedAll_of_vertex_of_jordanSchoenflies` (and its planar variant): the target
  `Work.BoxShrink.AeSlicedAll` of the chapter, with the (false)
  `Work.Smooth.Morse.CompactOneManifoldInput` hypothesis replaced by the theorem proved here;
* `ae_niceLevel`: the corrected form of `Work.BoxShrink.Pinch.BoxSliceNice` (which is ill-posed at
  the tangency levels, where the trace can be a finite set of points).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **Almost every box level is locally Euclidean of dimension one.** -/
theorem ae_isLocallyEuclidean_levelSet {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hvert : Work.Smooth.BoxGeneric.AeNoVertex ψ c σ) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsLocallyEuclidean (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  have hreg := Work.Smooth.BoxGeneric.FaceRegular.ae_face_regular_of_sardCoord
    (Work.Smooth.BoxGeneric.Sard.sardCoord ψ) c σ
  have hcorn := Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector (ψ := ψ) c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [hreg, hcorn, hvert, hne] with s hs_reg hs_corn hs_vert hs_ne
  rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact Work.Smooth.BoxGeneric.BoxSphere_eq_empty_of_neg hslt c σ
    have hempty : Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s = ∅ := by
      rw [Work.Smooth.Morse.levelSet, hbox, Set.inter_empty]
    rw [hempty]
    intro x
    exact absurd x.2 (Set.notMem_empty _)
  · exact isLocallyEuclidean_levelSet_of_regular hsgt (fun i ε hε => hs_reg i ε hε) hs_corn
      hs_vert

/-- **Almost every box level is a finite disjoint union of circles.** -/
theorem ae_isCircleUnion_levelSet {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hvert : Work.Smooth.BoxGeneric.AeNoVertex ψ c σ) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.IsCircleUnion ψ (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  have hloc := ae_isLocallyEuclidean_levelSet (ψ := ψ) (c := c) (σ := σ) hvert
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

/-- **Almost every box sphere meets the surface in general position**, with no input beyond the
genericity of the vertex stratum. -/
theorem aeTransverseBox_of_vertex {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hvert : Work.Smooth.BoxGeneric.AeNoVertex ψ c σ) :
    Work.Smooth.BoxGeneric.AeTransverseBox ψ c σ := by
  have hcirc := ae_isCircleUnion_levelSet (ψ := ψ) (c := c) (σ := σ) hvert
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

/-- **The target `Work.BoxShrink.AeSliced` of the box chapter**, from the vertex genericity and the
classical slicing input. -/
theorem aeSliced_of_vertex {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hvert : Work.Smooth.BoxGeneric.AeNoVertex ψ c σ)
    (hS : Work.Topology.SphereSlicing.SliceInput (Work.Smooth.Morse.torus ψ)) :
    Work.BoxShrink.AeSliced ψ c σ :=
  Work.Smooth.BoxGeneric.aeSliced_of_aeTransverseBox ψ c σ (aeTransverseBox_of_vertex hvert) hS

/-- **The target `Work.BoxShrink.AeSlicedAll` from the vertex genericity and the sphere-side
Jordan–Schoenflies theorem.** -/
theorem aeSlicedAll_of_vertex_of_jordanSchoenflies
    (hvert : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Work.Smooth.BoxGeneric.AeNoVertex ψ c σ)
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) :
    Work.BoxShrink.AeSlicedAll :=
  fun ψ c σ => aeSliced_of_vertex (hvert ψ c σ)
    (Work.Smooth.BoxGeneric.sliceInput_of_jordanSchoenflies hjordan ψ)

/-- **The target `Work.BoxShrink.AeSlicedAll` from the vertex genericity and the *planar*
Jordan–Schoenflies theorem.** -/
theorem aeSlicedAll_of_vertex_of_planeHypothesis
    (hvert : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Work.Smooth.BoxGeneric.AeNoVertex ψ c σ)
    (hplane : Work.Smooth.SphereJordan.PlaneHypothesis) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_vertex_of_jordanSchoenflies hvert
    (Work.Smooth.SphereJordan.jordanSchoenfliesSphere hplane)

end

end Work.Smooth.OneManifold

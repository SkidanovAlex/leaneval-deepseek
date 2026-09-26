import Submission.Work.Smooth.BoxGeneric.All
import Submission.Work.Smooth.Plane.All
import Submission.Work.Smooth.OneManifold.All

/-!
# Almost every cutting plane is transverse to the surface

This file carries out item (1) of the `Submission/Work/PlaneSlice` assignment: the **corrected,
non-vacuous** almost-everywhere transversality of a plane with respect to the surface
`F = ψ(standard torus)` of the challenge.

The chapters `Submission/Work/Smooth/BoxGeneric` and `Submission/Work/Smooth/Plane` state the
cutting-plane transversality with the hypothesis `Work.Smooth.Morse.CompactOneManifoldInput ψ`,
which is **false** for every `ψ` (`Work.Smooth.OneManifold.not_compactOneManifoldInput`): that
predicate allows the neighbourhood `U = univ`, so a figure eight qualifies.  The corrected route,
already assembled in the workspace, replaces it by the local `1`-manifold structure:

* two-dimensional Sard for the coordinate functions on the surface is a theorem
  (`Work.Smooth.BoxGeneric.Sard.sardCoord`);
* at a *regular* level of `g|_F` the level set is a topological `1`-manifold
  (`Work.Smooth.OneManifold.levelSet_isLocallyEuclidean_of_regularValue`) and compact
  (`Work.Smooth.Morse.Surface.isCompact_levelSet`);
* a compact locally Euclidean subset of the surface is a finite disjoint union of embedded circles
  (`Work.Smooth.OneManifold.isCircleUnion_of_isCompact_of_isLocallyEuclidean`), whence a
  transversality witness
  (`Work.Smooth.OneManifold.transverseSphere_of_isCompact_isLocallyEuclidean`);
* the sphere vocabulary implies the plane vocabulary
  (`Work.Smooth.BoxGeneric.PlaneTransverse.transversePlane_of_transverseSphere`).

## Main results

* `Work.PlaneSlice.ae_isCircleUnion_levelSet` — for every `ψ`, every `j` and every `a`, for almost
  every `u` the level set `F ∩ {y j = a + u}` is a finite disjoint union of embedded circles;
* `Work.PlaneSlice.ae_transverseSphere_coord` — the same in the `TransverseSphere` vocabulary;
* `Work.PlaneSlice.ae_transversePlane_coord` — for almost every `u`,
  `Work.Smooth.Plane.TransversePlane (torus ψ) {y | y j = a + u}`;
* `Work.PlaneSlice.ae_transversePlane_pardonSlice` — **item (1)**: for almost every plane level `u`,
  the cutting plane `{y | y (σ 2) = c (σ 2) + u}` of Pardon's box is transverse to the surface.

None of these takes any hypothesis beyond the data: they are unconditional, sorry-free and
axiom-free.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory
open scoped Topology

namespace Work.PlaneSlice

noncomputable section

/-- **Almost every level of a coordinate function on the surface is transverse to it.**

For every diffeomorphism `ψ`, every coordinate `j` and every real `a`, for almost every `u` the
plane `{y : R3 | y j = a + u}` meets the surface `F = ψ(standard torus)` in a finite disjoint union
of embedded circles of `F`, i.e. a `TransverseSphere` witness.

This is the corrected form of
`Work.Smooth.BoxGeneric.PlaneTransverse.ae_transverseSphere_coord`, whose hypothesis
`Work.Smooth.Morse.CompactOneManifoldInput ψ` is false for every `ψ`: here the classification of
compact `1`-manifolds is applied only at the *regular* levels supplied by Sard, where the local
structure is a theorem. -/
theorem ae_transverseSphere_coord (ψ : Submission.Diffeo) (j : Fin 3) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
        {y : R3 | y j = u} := by
  filter_upwards [Work.Smooth.BoxGeneric.Sard.sardCoord ψ j] with u hu
  have hg : ContDiff ℝ 1 (fun y : R3 => y j) := by fun_prop
  have hset : ({y : R3 | y j = u} ∩ (Work.Smooth.Morse.torus ψ).carrier) =
      Work.Smooth.Morse.levelSet ψ (fun y : R3 => y j) u := by
    rw [Work.Smooth.Morse.levelSet]
    exact Set.inter_comm _ _
  refine Work.Smooth.OneManifold.transverseSphere_of_isCompact_isLocallyEuclidean ψ ?_ ?_
  · rw [hset]
    exact Work.Smooth.Morse.Surface.isCompact_levelSet ψ hg.continuous u
  · rw [hset]
    exact Work.Smooth.OneManifold.levelSet_isLocallyEuclidean_of_regularValue ψ hg hu

/-- **Almost every level set of a coordinate function is a finite union of circles.**  The
`IsCircleUnion` form of `ae_transverseSphere_coord`; it is the hypothesis under which the slicing
of the box by the cutting plane is constructed. -/
theorem ae_isCircleUnion_levelSet (ψ : Submission.Diffeo) (j : Fin 3) (a : ℝ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.IsCircleUnion ψ
        (Work.Smooth.Morse.levelSet ψ (fun y : R3 => y j) (a + u)) := by
  have h := Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine (a := a) (b := 1) one_ne_zero
    (P := fun t => Work.Smooth.Morse.IsCircleUnion ψ
      (Work.Smooth.Morse.levelSet ψ (fun y : R3 => y j) t))
    (by
      filter_upwards [Work.Smooth.BoxGeneric.Sard.sardCoord ψ j] with u hu
      have hg : ContDiff ℝ 1 (fun y : R3 => y j) := by fun_prop
      exact Work.Smooth.OneManifold.levelSet_isCircleUnion_of_regularValue ψ hg hu)
  filter_upwards [h] with u hu
  rw [one_mul] at hu
  simpa [add_comm] using hu

/-- **Almost every plane `{y | y j = a + u}` is transverse to the surface.**

This is item (1) of the assignment, in the plane vocabulary of `Work.Smooth.Plane.TransversePlane`.
It is the corrected form of `Work.Smooth.BoxGeneric.PlaneTransverse.ae_transversePlane_coord`
(which assumes the false `Work.Smooth.Morse.CompactOneManifoldInput ψ`). -/
theorem ae_transversePlane_coord (ψ : Submission.Diffeo) (j : Fin 3) (a : ℝ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Plane.TransversePlane (Work.Smooth.Morse.torus ψ)
        {y : R3 | y j = a + u} := by
  have h := Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine (a := a) (b := 1) one_ne_zero
    (P := fun t => Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | y j = t}) (ae_transverseSphere_coord ψ j)
  filter_upwards [h] with u hu
  rw [one_mul] at hu
  have hset : {y : R3 | y j = u + a} = {y : R3 | y j = a + u} := by
    ext y; rw [add_comm]
  rw [hset] at hu
  exact Work.Smooth.BoxGeneric.PlaneTransverse.transversePlane_of_transverseSphere hu

/-- **Item (1): almost every cutting plane of Pardon's box is transverse to the surface.**

For every diffeomorphism `ψ`, every centre `c` and every coordinate permutation `σ`, for almost
every `u` the plane `{y : R3 | y (σ 2) = c (σ 2) + u}` — the plane by which Pardon's double-bubble
core cuts his box — is transverse to the surface `F = ψ(standard torus)` in the sense of
`Work.Smooth.Plane.TransversePlane`.

This is the corrected, non-vacuous form of
`Work.Smooth.BoxGeneric.PlaneTransverse.ae_transversePlane_pardonSlice` (whose hypothesis
`Work.Smooth.Morse.CompactOneManifoldInput ψ` is refuted by
`Work.Smooth.OneManifold.not_compactOneManifoldInput`). -/
theorem ae_transversePlane_pardonSlice (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Plane.TransversePlane (Work.Smooth.Morse.torus ψ)
        {y : R3 | y (σ 2) = c (σ 2) + u} :=
  ae_transversePlane_coord ψ (σ 2) (c (σ 2))

/-- The `IsCircleUnion` form of the cutting-plane general position: for almost every `u`, the
intersection of the surface with the cutting plane `{y (σ 2) = c (σ 2) + u}` is a finite disjoint
union of embedded circles.  This is the input from which the slicing of the slice of the box is
built in `Submission/Work/PlaneSlice/Slice.lean`. -/
theorem ae_isCircleUnion_pardonSlice (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.IsCircleUnion ψ
        (Work.Smooth.Morse.levelSet ψ (fun y : R3 => y (σ 2)) (c (σ 2) + u)) :=
  ae_isCircleUnion_levelSet ψ (σ 2) (c (σ 2))

end

end Work.PlaneSlice

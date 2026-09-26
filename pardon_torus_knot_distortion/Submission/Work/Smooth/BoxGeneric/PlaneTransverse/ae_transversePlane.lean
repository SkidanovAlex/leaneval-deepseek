import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Bridge
import Submission.Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_transverseSphere_coord
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_transverseSphere_face
import Submission.Work.Smooth.Plane.Slicing
import Submission.Work.Smooth.BoxGeneric.Sard.SardCoord

/-!
# Almost every cutting plane is transverse to the surface

Item 4 of the assignment: for every diffeomorphism `ψ`, centre `c` and coordinate permutation `σ`,
the cutting plane `{y | y (σ 2) = c (σ 2) + u}` is transverse to the surface `F = ψ(standard
torus)`, in the sense of `Work.Smooth.Plane.TransversePlane`, for almost every `u`.

The general position of the *sphere* `{y | boxNorm c σ · = s}` (the whole chapter) and that of the
*plane* are the two slices used by Pardon's sweep; both are obtained here from the same input: the
surface meets a plane in a compact `1`-manifold for almost every parallel plane
(`PlaneTransverse.ae_transverseSphere_coord`), and the classification of compact `1`-manifolds
(`Work.Smooth.Morse.CompactOneManifoldInput`).

The bridge from the sphere vocabulary to the planar one is
`Work.Smooth.BoxGeneric.transversePlane_of_transverseSphere`: a finite family of pairwise disjoint
simple closed curves covering `F ∩ D` is in particular a `Work.Smooth.Plane.TransversePlane` (take
no arcs); this is the case that occurs for a whole plane, whose intersection with `F` has no
boundary points.

## Main results

* `Work.Smooth.BoxGeneric.transversePlane_of_transverseSphere`;
* `Work.Smooth.BoxGeneric.ae_transversePlane_coord` — for almost every `u`, the plane
  `{y | y j = a + u}` is transverse to `F`;
* `Work.Smooth.BoxGeneric.ae_transversePlane_face` — for almost every `s`, each of the six face
  planes `{y | faceLin c σ i ε y = s}` is transverse to `F`;
* `Work.Smooth.BoxGeneric.ae_transversePlane_pardonSlice` — **item 4**: for almost every `u`, the
  cutting plane `{y | y (σ 2) = c (σ 2) + u}` is transverse to `F`.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory

namespace Work.Smooth.BoxGeneric.PlaneTransverse

/-- **The sphere vocabulary implies the planar one.**  A finite family of pairwise disjoint simple
closed curves of the surface covering `F ∩ D` is a `Work.Smooth.Plane.TransversePlane P D`: the
family of arcs is empty.

(Note that the converse is *false*: a planar region with boundary, such as the slice of Pardon's box
by the cutting plane, meets the surface in arcs as well as in closed curves; the arcs are the
`κ`-family of `TransversePlane`, which this lemma takes to be empty.) -/
theorem transversePlane_of_transverseSphere {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : Work.Topology.SphereSlicing.TransverseSphere P D) :
    Work.Smooth.Plane.TransversePlane P D := by
  obtain ⟨ι, hι, c, hsimple, hdisj, hmem, hcov⟩ := h
  refine ⟨ι, hι, c, PEmpty, inferInstance, PEmpty.elim, hsimple, hdisj, hmem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; exact PEmpty.elim j
  · intro j; exact PEmpty.elim j
  · intro j; exact PEmpty.elim j
  · intro j; exact PEmpty.elim j
  · intro j; exact PEmpty.elim j
  · intro x hxD hx
    exact Or.inl (hcov x hxD hx)

/-- **Almost every plane `{y | y j = a + u}` is transverse to the surface.**  This is
`Work.Smooth.BoxGeneric.PlaneTransverse.ae_transverseSphere_coord` (almost every level of the
coordinate function `y ↦ y j` is a regular value of the surface, hence the level set is a compact
`1`-manifold for almost every level, hence a finite disjoint union of simple closed curves), with the
plane `{y | y j = u}` reparametrised to `{y | y j = a + u}`. -/
theorem ae_transversePlane_coord {ψ : Submission.Diffeo}
    (hS : Work.Smooth.BoxGeneric.SardCoord ψ)
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) (j : Fin 3) (a : ℝ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Plane.TransversePlane (Work.Smooth.Morse.torus ψ)
        {y : R3 | y j = a + u} := by
  have h := PlaneTransverse.ae_transverseSphere_coord hS hclass j
  have h' := FaceRegular.ae_comp_affine (a := a) (b := 1) one_ne_zero
    (P := fun t => Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | y j = t}) h
  filter_upwards [h'] with u hu
  rw [one_mul] at hu
  have hset : {y : R3 | y j = u + a} = {y : R3 | y j = a + u} := by
    ext y; rw [add_comm]
  rw [hset] at hu
  exact transversePlane_of_transverseSphere hu

/-- **Almost every face plane of the box is transverse to the surface.** -/
theorem ae_transversePlane_face {ψ : Submission.Diffeo}
    (hS : Work.Smooth.BoxGeneric.SardCoord ψ)
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ∀ (i : Fin 3) (ε : ℝ),
      (ε = 1 ∨ ε = -1) →
        Work.Smooth.Plane.TransversePlane (Work.Smooth.Morse.torus ψ)
          {y : R3 | Work.Smooth.BoxGeneric.faceLin c σ i ε y = s} := by
  filter_upwards [PlaneTransverse.ae_transverseSphere_face hS hclass c σ] with s hs i ε hε
  exact transversePlane_of_transverseSphere (hs i ε hε)

/-- **Item 4: almost every cutting plane `{y | y (σ 2) = c (σ 2) + u}` is transverse to the
surface** `F = ψ(standard torus)`, in the sense of `Work.Smooth.Plane.TransversePlane`. -/
theorem ae_transversePlane_pardonSlice {ψ : Submission.Diffeo}
    (hS : Work.Smooth.BoxGeneric.SardCoord ψ)
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Plane.TransversePlane (Work.Smooth.Morse.torus ψ)
        {y : R3 | y (σ 2) = c (σ 2) + u} :=
  ae_transversePlane_coord hS hclass (σ 2) (c (σ 2))

/-- The same with the Sard input discharged by two-dimensional Sard. -/
theorem ae_transversePlane_pardonSlice' (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Plane.TransversePlane (Work.Smooth.Morse.torus ψ)
        {y : R3 | y (σ 2) = c (σ 2) + u} :=
  ae_transversePlane_pardonSlice (Sard.sardCoord ψ) hclass c σ

end Work.Smooth.BoxGeneric.PlaneTransverse

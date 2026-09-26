import Mathlib
import Submission.Work.Smooth.Plane.Slicing
import Submission.Work.Smooth.Plane.Slicing.planeSliceData_covers
import Submission.Work.Smooth.Plane.Slicing.planeSliceData_inside_subset

/-!
# From the classical slicing datum to the planar slicing

`Work.Smooth.Plane.PlaneSlicing P D` asks for the components of `F ∩ D` (closed curves *and* arcs),
the disc each closed component bounds inside `D`, the nesting rank, *and* two consequences of the
datum:

* `inside_subset` — a closed component meeting the interior of the disc of another is contained in
  it (proved from the Jordan separation field `open_interior`);
* `covers` — every loop of `F` inside `D` lies on one of the pieces (proved from the point-wise
  covering `covers_pt` by connectedness, with the arcs as further closed sets).

The structure `Work.Smooth.Plane.PlaneSliceData P D` records only the classical facts; this file
proves that it implies `PlaneSlicing P D`, so that the slicing input `PlaneSliceInput P` — every
convex planar region in general position admits a slicing datum — supplies the full planar slicing
`SlicedPlane P D`.

The proofs of the two consequences are `Work.Smooth.Plane.Slicing.planeSliceData_inside_subset` and
`Work.Smooth.Plane.Slicing.planeSliceData_covers`.

## Main results

* `planeSlicingOfSliceData` — the classical datum gives the planar slicing;
* `nonempty_planeSlicing_of_sliceData`, `nonempty_planeSlicing_of_sliceInput` — the `Nonempty`
  forms, i.e. `SlicedPlane P D` from the classical input;
* `innermostDiscInput_of_sliceData`, `innermostDiscInput_of_sliceInput` — Pardon's first innermost
  step for the planar region `D` (see also
  `Work.Smooth.Plane.innermostDiscInput_of_slicing`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Plane

noncomputable section

/-- **The planar slicing from the classical slicing datum.**  The two nontrivial fields `covers`
and `inside_subset` are proved from the datum; the remaining fields are the datum itself. -/
def planeSlicingOfSliceData {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : PlaneSliceData P D) : PlaneSlicing P D where
  ι := h.ι
  fintype := h.fintype
  c := h.c
  simple := h.simple
  disjoint := h.disjoint
  mem := h.mem
  disc := h.disc
  disc_inj := h.disc_inj
  disc_boundary := h.disc_boundary
  disc_mem := h.disc_mem
  rank := h.rank
  inside := h.inside
  inside_subset := fun i j hij => Work.Smooth.Plane.Slicing.planeSliceData_inside_subset h i j hij
  covers_interior := h.covers_interior
  κ := h.κ
  fintypeκ := h.fintypeκ
  a := h.a
  a_inj := h.a_inj
  a_mem := h.a_mem
  a_surface := h.a_surface
  a_disjoint := h.a_disjoint
  a_disjoint_c := h.a_disjoint_c
  covers := fun γ hγ => Work.Smooth.Plane.Slicing.planeSliceData_covers h γ hγ

/-- The slicing datum gives the planar slicing: `SlicedPlane P D`. -/
theorem nonempty_planeSlicing_of_sliceData {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : PlaneSliceData P D) : Nonempty (PlaneSlicing P D) :=
  ⟨planeSlicingOfSliceData h⟩

/-- **The planar slicing from the slicing input**, at every convex planar region in general position
with respect to `F`.  (The hypothesis `TransversePlane P D` cannot be dropped: for a region whose
intersection with `F` is two-dimensional no slicing exists.) -/
theorem nonempty_planeSlicing_of_sliceInput {P : Work.CoreTopology.ParamTorus}
    (h : PlaneSliceInput P) {D : Set R3} (hD : IsConvexPlanar D) (hT : TransversePlane P D) :
    Nonempty (PlaneSlicing P D) :=
  nonempty_planeSlicing_of_sliceData (h D hD hT).some

/-- **`SlicedPlane P D` from the slicing input**: the general-position form of the planar slicing. -/
theorem slicedPlane_of_sliceInput {P : Work.CoreTopology.ParamTorus} (h : PlaneSliceInput P)
    {D : Set R3} (hD : IsConvexPlanar D) (hT : TransversePlane P D) : SlicedPlane P D :=
  nonempty_planeSlicing_of_sliceInput h hD hT

/-! ## Non-vacuity of the slicing datum -/

/-- **The degenerate slicing.**  If the convex planar region `D` is disjoint from the surface
`F = P.carrier`, then it is sliced by `F` with no pieces at all: `PlaneSliceData P D` holds with
empty index types.  This is the planar analogue of
`Work.Topology.SphereSlicing.sliceDataOfDisjoint`, and it shows that the slicing datum of this
chapter is not vacuous. -/
def planeSliceDataOfDisjoint {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : ∀ x : R3, x ∈ D → x ∉ P.carrier) : PlaneSliceData P D where
  ι := Empty
  fintype := inferInstance
  c := fun i => isEmptyElim i
  simple := fun i => isEmptyElim i
  disjoint := fun i => isEmptyElim i
  mem := fun i => isEmptyElim i
  disc := fun i => isEmptyElim i
  disc_inj := fun i => isEmptyElim i
  disc_boundary := fun i => isEmptyElim i
  disc_mem := fun i => isEmptyElim i
  open_interior := fun i => isEmptyElim i
  covers_interior := fun i => isEmptyElim i
  κ := Empty
  fintypeκ := inferInstance
  a := fun j => isEmptyElim j
  a_inj := fun j => isEmptyElim j
  a_mem := fun j => isEmptyElim j
  a_surface := fun j => isEmptyElim j
  a_disjoint := fun j => isEmptyElim j
  a_disjoint_c := fun j => isEmptyElim j
  covers_pt := fun x hx hxc => (h x hx hxc).elim
  rank := fun i => isEmptyElim i
  inside := fun i => isEmptyElim i

/-- **A convex planar region disjoint from the surface is sliced by it** — unconditionally, with no
classical input: `SlicedPlane P D`. -/
theorem slicedPlane_of_disjoint {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : ∀ x : R3, x ∈ D → x ∉ P.carrier) : SlicedPlane P D :=
  nonempty_planeSlicing_of_sliceData (planeSliceDataOfDisjoint h)

/-- **A convex planar region disjoint from the surface contains no essential loop of it** —
unconditionally, with no classical input at all. -/
theorem not_containsEssentialLoop_of_disjoint {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : ∀ x : R3, x ∈ D → x ∉ P.carrier) : ¬ P.ContainsEssentialLoop D :=
  fun ⟨γ, _, hγ⟩ => h (γ.γ 0) (hγ 0) (γ.mem 0)

end

end Work.Smooth.Plane

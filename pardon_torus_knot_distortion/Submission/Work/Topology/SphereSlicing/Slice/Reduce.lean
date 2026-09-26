import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.sliceData_covers
import Submission.Work.Topology.SphereSlicing.sliceData_inside_subset

/-!
# The slicing of a sphere by the surface, from the classical datum

`Work.InnermostDisk.SphereSlicing P S` asks for fifteen fields: the components of `S ∩ F`, the
disc each of them bounds inside `S`, the nesting rank, *and* two consequences of those — that the
components cover every loop of `F` inside `S` (`covers`) and that the disc of a component contains
every other component meeting its interior (`inside_subset`).

The structure `Work.Topology.SphereSlicing.SliceData P S` records only the classical facts
(transversality, Jordan–Schoenflies, nesting).  This file proves that `SliceData P S` implies
`SphereSlicing P S`, by supplying the two consequences from the two proved lemmas

* `Work.Topology.SphereSlicing.sliceData_covers` (a loop of `F` inside `S` is connected and the
  component ranges are closed and pairwise disjoint);
* `Work.Topology.SphereSlicing.sliceData_inside_subset` (the interior of a disc is open in `S` and
  the disc is closed there, so a connected curve avoiding the boundary lies on one side);

and the trivial third consequence that the interior of a disc meets `F` only along components
(`covers_interior`, a direct consequence of `covers_pt`).

Hence `SphereSlicingInput P` follows from `SliceInput P`, and Pardon's first innermost input is
available at every embedded sphere — in particular at the box boundary, see
`Work.Topology.SphereSlicing.Assembly`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-- **The slicing of a sphere by the surface, from the classical datum.**  The two nontrivial
fields `covers` and `inside_subset` are proved from the datum (`sliceData_covers`,
`sliceData_inside_subset`); the remaining fields are the datum itself. -/
def sphereSlicingOfSliceData {P : ParamTorus} {S : Set R3} (h : SliceData P S) :
    SphereSlicing P S where
  ι := h.ι
  fintype := h.fintype
  c := h.c
  simple := h.simple
  disjoint := h.disjoint
  mem := h.mem
  covers := sliceData_covers h
  disc := h.disc
  disc_inj := h.disc_inj
  disc_boundary := h.disc_boundary
  disc_mem := h.disc_mem
  rank := h.rank
  inside := h.inside
  inside_subset := sliceData_inside_subset h
  covers_interior := fun i z hz hc => h.covers_pt (h.disc i z) (h.disc_mem i z) hc

/-- The slicing datum gives the PL slicing: `Nonempty (SphereSlicing P S)`. -/
theorem nonempty_sphereSlicing_of_sliceData {P : ParamTorus} {S : Set R3}
    (h : SliceData P S) : Nonempty (SphereSlicing P S) :=
  ⟨sphereSlicingOfSliceData h⟩

/-- **Pardon's `SphereSlicing` from the slicing input**, at every embedded sphere which is in
general position with respect to `F`.  (The hypothesis `TransverseSphere P S` cannot be dropped:
for a sphere whose intersection with `F` is two-dimensional no slicing exists, see the discussion
in `Work.Topology.SphereSlicing.Defs`.) -/
theorem nonempty_sphereSlicing_of_sliceInput {P : ParamTorus} (h : SliceInput P) {S : Set R3}
    (hS : IsEmbeddedSphere S) (hT : TransverseSphere P S) : Nonempty (SphereSlicing P S) :=
  nonempty_sphereSlicing_of_sliceData (h S hS hT).some

/-- **Pardon's first innermost input from the classical slicing datum.** -/
theorem innermostDiscInput_of_sliceData {P : ParamTorus} {S : Set R3} (h : SliceData P S) :
    InnermostDiscInput P S :=
  (nonempty_sphereSlicing_of_sliceData h).some.innermostDiscInput_of_slicing

/-- **Pardon's first innermost input at every embedded sphere in general position, from
`SliceInput`.** -/
theorem innermostDiscInput_of_sliceInput {P : ParamTorus} (h : SliceInput P) {S : Set R3}
    (hS : IsEmbeddedSphere S) (hT : TransverseSphere P S) : InnermostDiscInput P S :=
  innermostDiscInput_of_sliceData (h S hS hT).some

end

end Work.Topology.SphereSlicing

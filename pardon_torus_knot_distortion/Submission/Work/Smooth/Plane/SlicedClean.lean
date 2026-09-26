import Mathlib
import Submission.Work.Smooth.Plane.Cleaning
import Submission.Work.Smooth.Plane.SlicingReduce
import Submission.Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing

/-!
# The planar cleaning step from a slicing of the convex planar region

This file assembles item 3 of the planar chapter: **Pardon's cut-and-paste cleaning step for a
convex planar region** `D`, from

* a *slicing* of `D` by the surface (`Work.Smooth.Plane.PlaneSlicing P D`, i.e.
  `Work.Smooth.Plane.SlicedPlane P D`), which supplies Pardon's *first* innermost step
  (`Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing`), and
* the *cut-and-paste* (`Work.InnermostDisk.CleansDiscs P`, equivalently the single cut-and-paste
  `Work.Topology.SphereSlicing.CleanOneCurve P` or `Work.InnermostDisk.RemovesOneCurve P`), which is
  the global classical input of the workspace.

The two are combined by `Work.Smooth.Plane.cleansInConvexPlane_of_innermostDiscInput`, i.e. by
`Work.InnermostDisk.cleansInSphere_of_inputs'`, which is pure logic.

## Main results

* `cleansInConvexPlane_of_slicing` — the planar cleaning from a slicing of `D` and the cut-and-paste;
* `cleansInConvexPlane_of_slicedPlane` — the same from the general-position input
  `SlicedPlane P D`;
* `cleansInConvexPlane_of_planeSliceInput` — the same from the classical slicing input
  `PlaneSliceInput P` (general position `TransversePlane P D` made explicit);
* `cleansInConvexPlane_of_slicedPlane_cleanOneCurve`, `cleansInConvexPlane_of_slicedPlane_removesOneCurve`
  — the same with the *single* cut-and-paste in place of the iterated one.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Plane

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **Pardon's cleaning step in the convex planar region `D`, from a slicing of `D` and the
cut-and-paste.** -/
theorem cleansInConvexPlane_of_slicing {D : Set R3} (h : PlaneSlicing P D)
    (hcl : Work.InnermostDisk.CleansDiscs P) : CleansInConvexPlane P D :=
  cleansInConvexPlane_of_innermostDiscInput
    (Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing h) hcl

/-- **The planar cleaning from the general-position input `SlicedPlane P D`.** -/
theorem cleansInConvexPlane_of_slicedPlane {D : Set R3} (h : SlicedPlane P D)
    (hcl : Work.InnermostDisk.CleansDiscs P) : CleansInConvexPlane P D :=
  h.elim fun h' => cleansInConvexPlane_of_slicing h' hcl

/-- **The planar cleaning from the classical slicing input**: a convex planar region in general
position with respect to `F`, together with the cut-and-paste. -/
theorem cleansInConvexPlane_of_planeSliceInput (h : PlaneSliceInput P)
    (hcl : Work.InnermostDisk.CleansDiscs P) {D : Set R3} (hD : IsConvexPlanar D)
    (hT : TransversePlane P D) : CleansInConvexPlane P D :=
  cleansInConvexPlane_of_slicing (planeSlicingOfSliceData (h D hD hT).some) hcl

/-- **The planar cleaning from a slicing and the single cut-and-paste `CleanOneCurve`.** -/
theorem cleansInConvexPlane_of_slicedPlane_cleanOneCurve {D : Set R3} (h : SlicedPlane P D)
    (hClean : Work.Topology.SphereSlicing.CleanOneCurve P) : CleansInConvexPlane P D :=
  h.elim fun h' => cleansInConvexPlane_of_cleanOneCurve
    (Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing h') hClean

/-- **The planar cleaning from a slicing and the single cut-and-paste `RemovesOneCurve`.** -/
theorem cleansInConvexPlane_of_slicedPlane_removesOneCurve {D : Set R3} (h : SlicedPlane P D)
    (hRem : Work.InnermostDisk.RemovesOneCurve P) : CleansInConvexPlane P D :=
  h.elim fun h' => cleansInConvexPlane_of_removesOneCurve
    (Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing h') hRem

/-! ## The uniform (all-regions) forms -/

/-- **Pardon's first innermost step, uniformly over all convex planar regions in general
position**: if `D` is convex planar, lies in general position with respect to `F` and carries an
essential loop of `F`, then it carries an innermost one.  This is the uniform form which the
classical slicing input produces. -/
def PlaneInnermostTransverseInput (P : Work.CoreTopology.ParamTorus) : Prop :=
  ∀ D : Set R3, IsConvexPlanar D → TransversePlane P D → Work.InnermostDisk.InnermostDiscInput P D

/-- Pardon's first innermost step at every convex planar region in general position, from the
classical slicing input. -/
theorem innermostDiscInput_of_planeSliceInput (h : PlaneSliceInput P) {D : Set R3}
    (hD : IsConvexPlanar D) (hT : TransversePlane P D) :
    Work.InnermostDisk.InnermostDiscInput P D :=
  Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing (planeSlicingOfSliceData (h D hD hT).some)

/-- Pardon's first innermost step at every convex planar region which is sliced by `F`. -/
theorem innermostDiscInput_of_slicedPlane {D : Set R3} (h : SlicedPlane P D) :
    Work.InnermostDisk.InnermostDiscInput P D :=
  h.elim Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing

/-- **Pardon's planar innermost-disc input from the classical slicing input**, uniformly over all
convex planar regions in general position. -/
theorem planeInnermostTransverseInput_of_planeSliceInput (h : PlaneSliceInput P) :
    PlaneInnermostTransverseInput P :=
  fun D hD hT => innermostDiscInput_of_planeSliceInput h hD hT

/-- **Pardon's cleaning step in every convex planar region in general position**, from the
classical slicing input and the cut-and-paste. -/
theorem cleansInConvexPlaneTransverseInput_of_planeSliceInput (h : PlaneSliceInput P)
    (hcl : Work.InnermostDisk.CleansDiscs P) : CleansInConvexPlaneTransverseInput P :=
  fun D hD hT => cleansInConvexPlane_of_planeSliceInput h hcl hD hT

end

end Work.Smooth.Plane

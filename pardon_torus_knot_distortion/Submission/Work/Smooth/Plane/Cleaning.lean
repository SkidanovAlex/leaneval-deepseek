import Mathlib
import Submission.Work.Smooth.Plane.Slicing
import Submission.Work.InnermostDisk.All
import Submission.Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve

/-!
# Pardon's cut-and-paste cleaning in a convex planar region

This file delivers the planar form of Pardon's *second* innermost argument
(`Work.InnermostDisk.CleansDiscs`), i.e. the cut-and-paste by which an innermost essential loop of
`F` inside a convex planar region `D` is turned into a **simple essential loop of `F` inside `D`
bounding an embedded disc whose interior is disjoint from `F`** (an element of Pardon's set `U`).

The statement is

`CleansInConvexPlane P D` — every essential loop of `F` whose image lies in `D` can be replaced by a
simple essential loop with image in `D` which bounds a disc in the complement of `F`.

It is the exact planar analogue of `Work.InnermostDisk.CleansInSphere P S` (the two are
definitionally the same statement, only the name of the region changed), which is why the
reductions of `Work.InnermostDisk` apply verbatim.  The two ingredients are:

* **innermost selection** in the planar slice (`Work.Smooth.Plane.PlaneSlicing`, giving Pardon's
  first innermost step `Work.InnermostDisk.InnermostDiscInput P D`);
* **the cut-and-paste** itself, which is a global classical input of the workspace
  (`Work.InnermostDisk.CleansDiscs P`, equivalently the single cut-and-paste
  `Work.Topology.SphereSlicing.CleanOneCurve P` or `Work.InnermostDisk.RemovesOneCurve P`), applied
  to the innermost disc inside `D`.

The two are combined by `Work.InnermostDisk.cleansInSphere_of_inputs'`, which needs no geometry.

## Main definitions

* `CleansInConvexPlane P D` — Pardon's cleaning step for the planar region `D`;
* `CleansInConvexPlaneInput P` — the same, uniformly over all convex planar regions.

## Main results

* `cleansInConvexPlane_iff_cleansInSphere` — the definitional identity with the spherical form;
* `cleansInConvexPlane_of_innermostDiscInput` — first innermost step plus cut-and-paste give the
  planar cleaning;
* `cleansInConvexPlane_of_cleansDiscs` — the form in which a caller who disposes of the global
  cut-and-paste hypothesis needs it;
* `cleansInConvexPlane_of_cleanOneCurve` — the same from the *single* cut-and-paste
  `Work.Topology.SphereSlicing.CleanOneCurve`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Plane

noncomputable section

/-! ## Pardon's cleaning step in a convex planar region -/

/-- **Pardon's second innermost argument in a convex planar region.**

Every essential loop `α` of `F = P.carrier` whose image lies in the convex planar region `D` can be
replaced by a *simple* essential loop `α'` of `F` with image in `D` which bounds an embedded disc in
`ℝ³` whose interior is disjoint from `F` (Pardon's set `U` of compressing loops).

This is the planar counterpart of `Work.InnermostDisk.CleansInSphere`, and it is literally the same
statement with the region renamed — hence an `abbrev`, so that every result stated for
`CleansInSphere` applies to it without proof. -/
abbrev CleansInConvexPlane (P : Work.CoreTopology.ParamTorus) (D : Set R3) : Prop :=
  ∀ α : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P α →
    (∀ t : ℝ, α.γ t ∈ D) →
    ∃ α' : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsSimple P α' ∧
      Work.CoreTopology.IsEssential P α' ∧
      Work.CoreTopology.BoundsDiskInComplement P α' ∧ ∀ t : ℝ, α'.γ t ∈ D

/-- The planar cleaning statement is the spherical one with the region renamed. -/
theorem cleansInConvexPlane_iff_cleansInSphere (P : Work.CoreTopology.ParamTorus) (D : Set R3) :
    CleansInConvexPlane P D ↔ Work.InnermostDisk.CleansInSphere P D := Iff.rfl

/-- **Pardon's cleaning step, uniformly over all convex planar regions.** -/
def CleansInConvexPlaneInput (P : Work.CoreTopology.ParamTorus) : Prop :=
  ∀ D : Set R3, IsConvexPlanar D → CleansInConvexPlane P D

/-- **Pardon's cleaning step, uniformly over all convex planar regions *in general position***:
the uniform form which the classical slicing input `PlaneSliceInput P` and the cut-and-paste
`Work.InnermostDisk.CleansDiscs P` actually produce. -/
def CleansInConvexPlaneTransverseInput (P : Work.CoreTopology.ParamTorus) : Prop :=
  ∀ D : Set R3, IsConvexPlanar D → TransversePlane P D → CleansInConvexPlane P D

/-- The uniform general-position form gives the cleaning step at every region in general position. -/
theorem CleansInConvexPlaneTransverseInput.of_transverse {P : Work.CoreTopology.ParamTorus}
    {h : CleansInConvexPlaneTransverseInput P} {D : Set R3} (hD : IsConvexPlanar D)
    (hT : TransversePlane P D) : CleansInConvexPlane P D :=
  h D hD hT

/-- The (stronger) uniform form without transversality gives the general-position one. -/
theorem CleansInConvexPlaneTransverseInput.of_input {P : Work.CoreTopology.ParamTorus}
    {h : CleansInConvexPlaneInput P} : CleansInConvexPlaneTransverseInput P :=
  fun D hD _ => h D hD

/-! ## The reduction -/

/-- **Pardon's first innermost step plus the cut-and-paste give the planar cleaning.**

If the convex planar region `D` admits innermost discs
(`Work.InnermostDisk.InnermostDiscInput P D`, produced by `PlaneSlicing` in
`Work.Smooth.Plane.SlicingReduce`) and the global cut-and-paste step
`Work.InnermostDisk.CleansDiscs P` holds, then every essential loop of `F` inside `D` can be cleaned:
this is `Work.InnermostDisk.cleansInSphere_of_inputs'`, whose hypotheses are exactly these two. -/
theorem cleansInConvexPlane_of_innermostDiscInput {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (hIn : Work.InnermostDisk.InnermostDiscInput P D)
    (hCl : Work.InnermostDisk.CleansDiscs P) : CleansInConvexPlane P D :=
  Work.InnermostDisk.cleansInSphere_of_inputs' hIn (fun DD => hCl D DD)

/-- **The planar cleaning from the global cut-and-paste and the innermost-disc input at every
region.** -/
theorem cleansInConvexPlane_of_forall_innermostDiscInput {P : Work.CoreTopology.ParamTorus}
    (hIn : ∀ D : Set R3, Work.InnermostDisk.InnermostDiscInput P D)
    (hCl : Work.InnermostDisk.CleansDiscs P) : CleansInConvexPlaneInput P :=
  fun D _ => cleansInConvexPlane_of_innermostDiscInput (hIn D) hCl

/-- **The planar cleaning from the single cut-and-paste `CleanOneCurve`.**

`Work.Topology.SphereSlicing.CleanOneCurve P` is Pardon's second innermost argument in the local
form of `Work.Topology.SphereSlicing.SliceDisc`; `Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve`
turns it into the global `CleansDiscs P`, and then
`cleansInConvexPlane_of_innermostDiscInput` applies. -/
theorem cleansInConvexPlane_of_cleanOneCurve {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (hIn : Work.InnermostDisk.InnermostDiscInput P D)
    (hClean : Work.Topology.SphereSlicing.CleanOneCurve P) : CleansInConvexPlane P D :=
  cleansInConvexPlane_of_innermostDiscInput hIn
    (Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve hClean)

/-- **The planar cleaning from the single cut-and-paste `RemovesOneCurve`.** -/
theorem cleansInConvexPlane_of_removesOneCurve {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (hIn : Work.InnermostDisk.InnermostDiscInput P D)
    (hRem : Work.InnermostDisk.RemovesOneCurve P) : CleansInConvexPlane P D :=
  cleansInConvexPlane_of_innermostDiscInput hIn
    (Work.InnermostDisk.cleansDiscs_of_removesOneCurve hRem)

end

end Work.Smooth.Plane

import Submission.Work.BoxShrink.Core.Basic

/-!
# The double-bubble local model, as a hypothesis of the reduction

Pardon's shrinking step consumes two geometric inputs at the boundary sphere `S = ∂PBox s c σ` and
at the slicing disc `D = PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}`:

* the classical innermost-disc input (`Work.InnermostDisk.CleansInSphere`) at `S` and at `D`, which
  turns the intersection counts produced by the sweep (`Work.BoxSweep.sweep`) into Pardon's `must
  be inessential` conclusion — that every curve of `F` inside `S` (resp. inside the flat disc `D`)
  is inessential;
* **Pardon's double bubble, in the "one surgery family" form**: given that the cuts are inessential,
  the region `F ∩ int(S)` inside the box can be deformed to the union of the two half-regions
  `F ∩ int(H₁) ∪ F ∩ int(H₂)` along a one-parameter family whose local moves are either
  loop-equivalences (`Work.SurgeryInvariance.RegionEquivalent`: no surgery) or the addition/removal
  of an open piece of `F` of vanishing winding span (`Work.SurgeryInvariance.SurgeryStepZero`: a
  single `2`-surgery).  That is the structure `BubbleSweep` below, which is a `SweepLoops` of the
  sibling subproject `Work.SurgeryInvariance` pinned down at the two endpoints.

`Work.SurgeryInvariance.SweepLoops.windingSpan_eq` then gives at once that the winding span is
constant along the family, so the essential loop inside the sphere survives to the union of the two
half-regions; since the two half-regions are open and disjoint, one of them must carry it
(`Bubble/Persistence`).

The structure `DoubleBubbleDatum` records the same content at the loop level
(`RegionEquivalent P (boxRegion) (upperRegion ∪ lowerRegion)`), and
`Bubble/Persistence.regionEquivalent_of_bubbleSweep` shows that `BubbleSweep` is the stronger,
"local models"-flavoured form.

The last structure, `BubbleInput`, is the complete set of hypotheses of the main theorem
`Work.BoxShrink.Core.crux_of_bubbleInput`: the classical innermost input at all boundary spheres and
all slicing discs, and the double-bubble family for every box/plane configuration in which the two
cuts are inessential.  See the README of this directory.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Core

noncomputable section

/-- **Pardon's double bubble, as a family of regions with the local models.**

This is the local-model datum that `Work.BoxShrink.CruxStatement` still consumes: a loop-level
sweep (`Work.SurgeryInvariance.SweepLoops`) whose initial region is the region of the surface inside
the sphere `∂PBox s c σ` and whose final region is the union of the two half-regions cut out by the
plane `{y (σ 2) = c (σ 2) + u}`.

Geometrically the family is Pardon's: the sphere `∂PBox s c σ` is pinched along the flat disc
`cutDisc s c σ u`, the intermediate spheres sweep through `F`, and at the pinching parameter the
region gains or loses the trace of an open piece of `F` of vanishing winding span.  The two
endpoints are forced by the geometry: `int(∂PBox s c σ) = PBox s c σ`, and the two halves of the
double bubble bound the two half-bodies `H₁, H₂` whose interiors are the two half-boxes, so that
`F ∩ int(H₁) ∪ F ∩ int(H₂) = upperRegion ∪ lowerRegion`. -/
structure BubbleSweep (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) where
  /-- the one-parameter family of regions, with its finitely many surgeries -/
  sweep : Work.SurgeryInvariance.SweepLoops P
  /-- at time `0` the family is the region inside the sphere `∂PBox s c σ` -/
  zero : sweep.region 0 = boxRegion P s c σ
  /-- at time `1` the family is the union of the two half-regions -/
  one : sweep.region 1 = upperRegion P s c σ u ∪ lowerRegion P s c σ u

/-- **The double-bubble datum in loop form**: the region inside the sphere and the union of the two
half-regions carry the same loops, with the same winding vectors.  This is the conclusion of
Pardon's `spherefamily`/`doublebubble` at the level of loops, and it is weaker than `BubbleSweep`
(which also exhibits the interpolating family and its local models). -/
def DoubleBubbleDatum (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  Work.SurgeryInvariance.RegionEquivalent P (boxRegion P s c σ)
    (upperRegion P s c σ u ∪ lowerRegion P s c σ u)

/-- **The hypotheses of the reduction of `Work.BoxShrink.CruxCore`.**

The sibling module `Submission.Work.BoxShrink.crux` supplies, as hypotheses of its `CruxCore`, the
general position of the swept sphere (`Work.BoxShrink.SlicedSphere`, i.e. a
`Work.InnermostDisk.SphereSlicing` of `{y | boxNorm c σ y = s}`) and Pardon's cut-and-paste step at
the surface (`Work.InnermostDisk.CleansDiscs`); together these give the classical innermost-disc
input `CleansInSphere` **at the boundary sphere** (see
`cleansInSphere_of_slicedSphere_and_cleansDiscs` below).  What remains for the double bubble is:

* `cleansInDisc` — the same classical innermost-disc input at the *flat disc*
  `cutDisc s c σ u` cut out of the box by the plane.  This is the *planar* form of Pardon's
  innermost argument (Jordan–Schoenflies in a disc, plus the same cut-and-paste); it is needed
  because the plane slice can carry essential loops (a plane through the origin meets the standard
  torus in a longitude), which is exactly what Pardon's count on the plane rules out;
* `bubble` — Pardon's double bubble for the pair `(sphere, disc)`: **given** that the sphere and
  the slice carry no essential loop (which is what the intersection counts of
  `Work.BoxSweep.sweep` deliver through the two innermost inputs), the family of regions pinching
  the sphere along the disc exists and its local models hold.  This is the remaining topological
  content of Pardon's Lemmas 2.1 and 3, in the loop-level vocabulary of
  `Work.SurgeryInvariance`; see the README of this directory for exactly which construction is
  missing and why. -/
structure BubbleInput where
  /-- the classical (planar) innermost-disc input at every flat disc cut out of a box by a plane -/
  cleansInDisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.InnermostDisk.CleansInSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (cutDisc s c σ u)
  /-- Pardon's double bubble, for every box/plane configuration whose two cuts are inessential -/
  bubble : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (sliceRegion P s c σ u) →
    BubbleSweep P s c σ u

/-- **The same datum as `BubbleInput`, but with the double bubble supplied as a family of *spheres*
with the local models of the library's `Work.SurgeryInvariance.Sweep`** (between exceptional
parameters the region is moved by an ambient isotopy of `ℝ³` preserving `F`; at an exceptional
parameter it gains or loses the interior of an embedded disc of `F`).  The conversion to
`BubbleInput.bubble` is `Work.SurgeryInvariance.Sweep.toLoops`, so either formulation of the local
model suffices for the reduction (`Work.BoxShrink.Core.cruxCore_of_physicalInput`). -/
structure PhysicalBubbleInput where
  /-- the classical (planar) innermost-disc input at every flat disc cut out of a box by a plane -/
  cleansInDisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.InnermostDisk.CleansInSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (cutDisc s c σ u)
  /-- Pardon's double bubble as a family of *spheres* with the local models of
  `Work.SurgeryInvariance.Sweep` -/
  bubbleSweep : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (sliceRegion P s c σ u) →
    ∃ sw : Work.SurgeryInvariance.Sweep P,
      sw.region 0 = boxRegion P s c σ ∧
        sw.region 1 = upperRegion P s c σ u ∪ lowerRegion P s c σ u

/-- **The classical input at a sphere in general position.**

A sphere sliced by the surface (`Work.InnermostDisk.SphereSlicing`) together with Pardon's
cut-and-paste step at the surface (`Work.InnermostDisk.CleansDiscs`) give the innermost-disc input
`CleansInSphere` at that sphere: the first step selects an innermost essential curve, the second
cleans its disc.  In particular the two hypotheses of `Work.BoxShrink.CruxCore` at the boundary
sphere of the box give its `CleansInSphere`. -/
theorem cleansInSphere_of_slicedSphere_and_cleansDiscs {P : Work.CoreTopology.ParamTorus}
    {S : Set R3}
    (hS : Nonempty (Work.InnermostDisk.SphereSlicing P S))
    (hcl : Work.InnermostDisk.CleansDiscs P) :
    Work.InnermostDisk.CleansInSphere P S :=
  Work.InnermostDisk.cleansInSphere_of_inputs
    (Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing hS.some) hcl

/-- **A disc in general position with respect to the surface**: the surface meets it in finitely
many pairwise disjoint simple closed curves, each bounding a disc inside it, nested.  This is
`Work.Topology.SphereSlicing.SliceData` — the planar form of "the sphere is in general position" —
whose nonemptiness is the hypothesis under which Pardon's innermost argument applies to the flat
slicing disc. -/
def SlicedDisc (P : Work.CoreTopology.ParamTorus) (D : Set R3) : Prop :=
  Nonempty (Work.Topology.SphereSlicing.SliceData P D)

/-- **The classical input at a disc in general position.**

A disc sliced by the surface (`Work.Topology.SphereSlicing.SliceData`) together with the single
cut-and-paste step (`Work.Topology.SphereSlicing.CleanOneCurve`) give the innermost-disc input
`CleansInSphere` at that disc: the first step selects an innermost essential curve, the second
cleans its disc.  This is the planar counterpart of
`cleansInSphere_of_slicedSphere_and_cleansDiscs` and it is what replaces the hypothesis
`BubbleInput.cleansInDisc` when the classical inputs are stated in the form of
`Work.Topology.SphereSlicing`. -/
theorem cleansInSphere_of_slicedDisc_and_cleanOneCurve {P : Work.CoreTopology.ParamTorus}
    {D : Set R3} (hD : SlicedDisc P D)
    (hcl : Work.Topology.SphereSlicing.CleanOneCurve P) :
    Work.InnermostDisk.CleansInSphere P D :=
  Work.Topology.SphereSlicing.cleansInSphere_of_sliceData hD.some hcl

end

end Work.BoxShrink.Core

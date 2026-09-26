import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.BoxShrink.Core.Basic
import Submission.Work.BoxShrink.Core.Counting.encard_lt_natCast_of_coe_le_ofReal
import Submission.Work.BoxShrink.Core.Counting.Basic
import Submission.Work.BoxShrink.Core.Counting.Sphere
import Submission.Work.BoxShrink.Core.Counting.Disc
import Submission.Work.BoxShrink.Core.Bubble.Defs
import Submission.Work.BoxShrink.Core.Bubble.Persistence
import Submission.Work.BoxShrink.Core.Bubble.Instances
import Submission.Work.BoxShrink.Core.Crux

/-!
# `Work.BoxShrink.Core` — the double-bubble core of Pardon's shrinking step

Entry point: import `Submission.Work.BoxShrink.Core.All`.  See
`Submission/Work/BoxShrink/Core/README.md` for the prose account, in particular for the exact
hypotheses that remain and why they are the honest content of Pardon's Lemmas 2.1 and 3.

## The vocabulary

* `upperHalf c σ u`, `lowerHalf c σ u`, `cutPlane c σ u` — the two open half-spaces and the cutting
  plane `{y | y (σ 2) = c (σ 2) + u}`;
* `sphereSet c σ s = {y | boxNorm c σ y = s}` — the boundary sphere `∂PBox s c σ` (the same set as
  `Work.Topology.SphereSlicing.BoxSphere`);
* `cutDisc s c σ u` — the flat disc `PBox s c σ ∩ cutPlane c σ u`, the disc glued to the sphere to
  form Pardon's double bubble;
* `boxRegion P s c σ`, `upperRegion P s c σ u`, `lowerRegion P s c σ u`, `sliceRegion P s c σ u` —
  the traces on the surface `F = P.carrier` of the inside of the sphere, of the two halves of the
  double bubble, and of the slicing disc.

## The local model

* `BubbleSweep P s c σ u` — Pardon's double bubble as a family of regions with the local models of
  `Work.SurgeryInvariance.SweepLoops`: the region inside the sphere is deformed to the union of the
  two half-regions along a family whose local moves are loop-equivalences or additions/removals of
  open pieces of vanishing winding span;
* `DoubleBubbleDatum P s c σ u` — the same content at the level of loops
  (`RegionEquivalent P (boxRegion) (upperRegion ∪ lowerRegion)`);
* `BubbleInput` — the complete input of the reduction: the planar innermost-disc input at the
  slicing disc, and the double bubble (for every configuration whose two cuts are inessential);
  `PhysicalBubbleInput` is the same with the double bubble supplied through the library's
  `Work.SurgeryInvariance.Sweep` (ambient isotopies and embedded discs) instead of `SweepLoops`;
* `SlicedDisc P D` — the planar general position datum (`Work.Topology.SphereSlicing.SliceData`).

## Main results

* `cruxCore_of_bubbleInput : BubbleInput → ∀ p q, Work.BoxShrink.CruxCore p q` — **the
  double-bubble core from the bubble input**;
* `cruxCore_of_hypotheses`, `cruxCore_of_sliceData`, `cruxCore_of_physicalInput` — the same with the
  input unpacked, with the planar innermost input in the classical `SliceData`/`CleanOneCurve` form,
  resp. with the double bubble in the `Work.SurgeryInvariance.Sweep` form;
* `crux_of_bubbleInput` (and `crux`) `: BubbleInput → CleansDiscsAll → AeSlicedAll →
  ∀ p q, Work.BoxShrink.CruxStatement p q` — the requested node of the challenge;
* `containsEssentialLoop_half_of_bubbleSweep`, `windingSpan_eq_of_bubbleSweep` — the
  double-bubble persistence in the region vocabulary;
* `not_containsEssentialLoop_sphereSet(_of_slicing)`, `not_containsEssentialLoop_sliceRegion` —
  the two counting consequences of `Work.BoxSweep.sweep` (Pardon's Lemma 4.2 at the boundary sphere
  and at the slicing disc);
* `bubbleSweep_of_doubleBubbleDatum`, `bubbleSweep_of_empty_slice`,
  `exists_essential_half_of_empty_slice` — content and non-vacuity of the local model;
* `cleansInSphere_of_slicedSphere_and_cleansDiscs`,
  `cleansInSphere_of_slicedDisc_and_cleanOneCurve` — the bridges from the general-position
  vocabularies to `CleansInSphere`;
* `containsEssentialLoop_upperRegion_iff`, `containsEssentialLoop_lowerRegion_iff`,
  `hasEssBox_iff`, `boxRegion_eq_union`, `isOpenInCarrier_boxRegion`, … — the elementary geometry.
-/

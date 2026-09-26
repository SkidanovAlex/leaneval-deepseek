import Submission.Work.CountedPinch.Defs
import Submission.Work.CountedPinch.Routes
import Submission.Work.CountedPinch.Arcs
import Submission.Work.CountedPinch.Instances
import Submission.Work.CountedPinch.Negative
import Submission.Work.CountedPinch.tameSlice_of_slicedPlane
import Submission.Work.CountedPinch.transversePlane_of_arcs
import Submission.Work.CountedPinch.not_containsEssentialLoop_of_arcs
import Submission.Work.CountedPinch.not_exists_compressingLoop_in_flatDisc
import Submission.Work.CountedPinch.not_sliceArcsBody_of_isCompact
import Submission.Work.CountedPinch.not_finiteCrossing_std
import Submission.Work.CountedPinch.transverseSlice_std_four
import Submission.Work.CountedPinch.exists_lt_mem_of_isOpen_Icc_zero
import Submission.Work.CountedPinch.oneSided_of_arcEndpoint
import Submission.Work.CountedPinch.tameSlice_standard_equator
import Submission.Work.CountedPinch.StdLocalDefs
import Submission.Work.CountedPinch.sliceArcsBody_standard_local
import Submission.Work.CountedPinch.innermostDiscInput_standard_equator

/-!
# `Work.CountedPinch` — the counted residual of Pardon's Lemma 3, sharpened to the general position
of the cutting plane

Entry point: `import Submission.Work.CountedPinch.All`.
Namespace `Work.CountedPinch`, directory `Submission/Work/CountedPinch/`.
See `README.md` for the full account.

## The two spellings of the residual

At every configuration carrying the counting data of the crux (the shell `CountedD`/`Counted`,
binder for binder the shell `Work.PinchFamily.Residual` of the previous chapters):

* **`Work.CountedPinch.CountedSlicePlane`** (equivalently its weaker spellings
  `Work.CountedPinch.CountedPlaneInput`, `Work.CountedPinch.CountedPlaneInputUniform`): the cutting
  plane meets the surface transversely along the slice, and the flat disc cut out of the box by the
  plane is sliced by the surface (resp. is innermost-complete).  This is the *compact* case: the
  workspace's tameness predicate forces the slice to be compact
  (`Work.CountedPinch.isCompact_slice_of_tameSlice`, i.e. the trace does not leave the box).
* **`Work.CountedPinch.CountedSliceArcs`** (with `Work.CountedPinch.CountedSliceCrossing`): the
  closure of the slice is a finite disjoint union of embedded arcs of the surface, closed at the
  ends.  This is the *honest* structure of a trace that leaves the open box, and the case of
  Pardon's finger move.

## The main results

* `Work.CountedPinch.pinchTransport_of_countedSlicePlane`,
  `Work.CountedPinch.pinchTransport_of_countedPlaneInput` — Pardon's push-off
  (`Work.PinchFamily.PinchTransport`), the local residual `Work.PinchCounted.CountedPinch`, Pardon's
  Lemma 3 in the counted form `Work.BoxShrink.Pinch.CountingHalf`, the crux and the challenge, from
  the plane datum.  On this route the two *endpoint* inessentiality facts of Pardon's Lemma 2 are
  **derived** from the counting: `Work.CountedPinch.sliceTrace_inessential_of_slicedPlane` uses the
  *plane count* of the counted configuration, and `Work.CountedPinch.regionPushOff_of_planeData` is
  the same reduction without the box-sphere hypotheses.
* `Work.CountedPinch.countingHalf_of_countedSliceArcs`, `..._of_countedSliceArcs` for the crux and
  the challenge — the same conclusion from the honest arc structure, where the counting is used only
  for the *sphere* trace (`Work.PinchCounted.sphereTrace_inessential_of_counts`), and the slice's
  inessentiality and tameness are free (`Work.CountedPinch.no_essential_of_sliceArcsBody`,
  `Work.CountedPinch.tameClosedSlice_of_sliceArcsBody`).
* `Work.CountedPinch.not_exists_compressingLoop_in_flatDisc` — the counting forbids a compressing
  loop of the surface inside the flat disc (Pardon's counting argument at the cutting disc).
* non-vacuity: `Work.CountedPinch.countedSlicePlane_of_disjoint` and the `..._of_disjoint` family.
* negative results: `Work.CountedPinch.not_forall_transverseSlice`,
  `Work.CountedPinch.not_forall_regionPushOff`, and — machine-checked — the unusability of the
  naive arcs datum (`Work.CountedPinch.not_sliceCompactArcsBody_of_not_isCompact`).
-/

namespace Work.CountedPinch

end Work.CountedPinch

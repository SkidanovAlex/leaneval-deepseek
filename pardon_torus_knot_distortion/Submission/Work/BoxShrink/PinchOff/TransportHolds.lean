import Submission.Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice
import Submission.Work.BoxShrink.PinchOff.SpanNeBot

/-!
# The transport datum of the pinch is a theorem (`TameSlice` case)

`Work.BoxShrink.Pinch.RegionTransportSpanBotTame` — the *first* component of the pair named in the
assignment, and the only one of the deliverable's three named targets that was neither refuted nor
inhabited — is the loop-level transport of the pinch in Pardon's trivially-pinching case
(`W(planeTrace) = ⊥`): every winding class realised in the box region is realised by a single loop
of one of the two half-regions.

With the honest tameness predicate `TameSlice` the slice is compact and therefore a finite disjoint
union of *inessential* circles, and the loop-level peeling of the slice
(`regionEquivalent_halves_of_tameSlice`, proved from `peel_curve_sdiff_discRegion`,
`CompactSlice.sliceCirclesOnly_of_isCompact` and `Extras.exists_discRegion_of_not_isEssential`)
gives exactly that transport.  The second component, `TraceClassBoundSpanNeBot`, is a theorem of
`SpanNeBot.lean`.  Hence the pair named in the assignment is inhabited:

* `regionTransportSpanBotTame_holds : Work.BoxShrink.Pinch.RegionTransportSpanBotTame`;
* `traceClassBoundSpanNeBot_holds : Work.BoxShrink.Pinch.TraceClassBoundSpanNeBot` (`SpanNeBot.lean`).

`TameSlice` is the hypothesis the parent chapter carries; it is *too strong* for Pardon's genuine
configurations (it excludes the open arcs of a real trace — see `README.md` §21, §31), which is why
the *un*counted residual `KeyTameClosed` (= `DropCase`, `Drop.lean`) is still open.  The transport
form was refuted earlier only *without* tameness (`Refute.lean`, `not_transport`), and that witness
has a slice of two open arcs.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The transport datum of the pinch, in the case the parent chapter carries.** -/
theorem regionTransportSpanBotTame_holds :
    Work.BoxShrink.Pinch.RegionTransportSpanBotTame :=
  fun ψ s c σ u hT hTa _hS hZ _ =>
    regionEquivalent_halves_of_tameSlice (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u) hT hTa hZ

/-- **The pair named in the assignment is inhabited**: the transport datum and the per-class bound
with the parent's tameness predicate. -/
theorem transport_and_classBound_hold :
    Work.BoxShrink.Pinch.RegionTransportSpanBotTame ∧
      Work.BoxShrink.Pinch.TraceClassBoundSpanNeBot :=
  ⟨regionTransportSpanBotTame_holds, traceClassBoundSpanNeBot_holds⟩

end

end Work.BoxShrink.PinchOff

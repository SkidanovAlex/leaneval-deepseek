import Submission.Work.BoxShrink.PinchOff.Honest

/-!
# The assignment's second named target component: `TraceClassBoundSpanNeBot` is inhabited

The deliverable named in the assignment lists three alternatives, the second of which is the pair
`Work.BoxShrink.Pinch.RegionTransportSpanBotTame` + `Work.BoxShrink.Pinch.TraceClassBoundSpanNeBot`.
This module inhabits the **second component** of that pair: at a transverse configuration whose
slice is *tame* in the parent chapter's sense (`TameSlice`) and whose slice carries no essential
loop, the honest residual holds — `traceClassBound_of_tameSlice` (`Honest.lean`, from the
compact-slice theorem `tracePerpRealisable_of_isCompact_slice` and the circles-only theorem
`windingSpan_omega_eq_halves_of_trace_circles`).

**The caveat, which is the reason the whole `RefuteNC` package exists.**  `TameSlice` parametrises
the pieces of the trace over the compact interval *and requires their ranges to lie in the slice*,
so it forces the slice to be compact (`isCompact_sliceRegion_of_tameSlice`), and the arcs
configurations — the ones Pardon's Lemma 3 is about — are excluded.  Moreover `TameSlice` is not a
weaker hypothesis that could be replaced by `TameClosedSlice`: the residual with `TameClosedSlice`
and without `hS` is *false* (`RefuteNC/Main.lean`, `not_tracePerpSliceBox`).  So this module
records a genuine inhabitant of the assignment's `TraceClassBoundSpanNeBot`, with the honest
statement of what its hypothesis costs.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **`TraceClassBoundSpanNeBot` is inhabited**: the honest per-class residual at a transverse, tame
configuration with an inessential slice, from `traceClassBound_of_tameSlice` (which does not use the
parent chapter's `TraceClassBoundSpanBot`, and needs no trace-line hypothesis). -/
theorem traceClassBoundSpanNeBot_holds :
    Work.BoxShrink.Pinch.TraceClassBoundSpanNeBot :=
  fun _ψ _s _c _σ _u hT hTa _hS hZ _hne => traceClassBound_of_tameSlice hT hTa hZ

/-- The parent chapter's `TraceClassBoundTame`, in the tamed setting. -/
theorem traceClassBoundTame_of_tameSlice
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    Work.BoxShrink.Pinch.TraceClassBoundTame :=
  traceHonestSlice_of_tameSlice htame

end

end Work.BoxShrink.PinchOff

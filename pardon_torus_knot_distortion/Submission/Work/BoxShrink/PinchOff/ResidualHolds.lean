import Submission.Work.BoxShrink.PinchOff.windingSpan_inf_span_le_halves_of_transverseSlice
import Submission.Work.BoxShrink.PinchOff.SliceCover
import Submission.Work.BoxShrink.Pinch.TameTarget

/-!
# The residual is a theorem: the slices of tame configurations are compact

`SliceCover.lean` proves that the slice of a configuration carrying a *transverse plane* is compact:
the tameness datum `TameSlice` is a `Work.Smooth.Plane.TransversePlane` for the flat disc of the box,
and its data cover the slice by finitely many images of the **compact** interval
`Work.Smooth.Plane.ArcInterval` (`isCompact_sliceRegion_of_tameSlice`).  Consequently

* the hypothesis `¬ IsCompact (Sigma ψ s c σ u)` — the "non-compact slice" case into which
  `CompactSlice.lean` isolated the residual, i.e. the case in which the trace of the cutting plane
  *leaves* the box and the slice consists of arcs open at their ends — is **inconsistent with
  `TameSlice`**: the arcs case does not occur in the tamed setting;
* at a compact slice the residual is the circles-only case of `CirclesCase.lean`
  (`tracePerpRealisable_of_isCompact_slice`), so the box-local residual `TracePerpSlice` is a
  theorem (`tracePerpSlice_holds`, in
  `Submission.Work.BoxShrink.PinchOff.windingSpan_inf_span_le_halves_of_transverseSlice`), and with
  it the whole chain of the chapter:
  * `TracePeriodBound` — the per-class bound,
  * `KeyTame` — the tamed dimension bound,
  * `SmoothHalfSTame` — Pardon's Lemma 3 for the smooth tori in general position,
  * `Work.BoxShrink.Pinch.PushOffHalfTame` — the parent chapter's name for the corrected field.

**The caveat, which matters more than the theorems.**  The proof above is short *because the
hypothesis is too strong*: `TameSlice` (like `SliceArcsOnly` in §19) parametrises the pieces of the
trace over a compact interval and demands that their ranges lie in the slice, so it forces the slice
to be compact, and a compact slice under `TransverseSlice` is a finite union of circles.  The case
Pardon's Lemma 3 is about — the cutting plane's trace *leaving* the box, so that the slice is a
finite union of arcs whose ends run to `∂PBox` — is therefore **excluded by the hypotheses**, and
the geometry of the pinch (the crossing parity and the pairing of the crossings, `README.md` §18.2
and §20) never has to be invoked.  A faithful formalisation of Pardon's general position has to
allow arcs that are *open* at their ends, i.e. a slice which is not compact; the statement that then
remains open is `TraceNonCompactSlice` of `CompactSlice.lean`, and it is *vacuously* implied by the
present hypotheses only because `TameSlice` is too strong.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The slice of a tame configuration is compact** — the fact which makes the tamed residual a
theorem, and which shows that the arcs of a genuine trace (open at their ends) are excluded by
`TameSlice`. -/
theorem isCompact_sigma_of_tameSlice (hTa : Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    IsCompact (Sigma ψ s c σ u) :=
  isCompact_sliceRegion_of_tameSlice hTa

/-- The "non-compact slice" case of `CompactSlice.lean` is empty in the tamed setting. -/
theorem not_not_isCompact_sigma_of_tameSlice (hTa : Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    ¬ ¬ IsCompact (Sigma ψ s c σ u) :=
  fun h => h (isCompact_sigma_of_tameSlice hTa)

/-- **The per-class bound is a theorem**: at every transverse, tame configuration whose slice
carries no essential loop, every multiple of a trace period realised in the box region is realised in
the halves. -/
theorem tracePeriodBound_holds : TracePeriodBound := by
  intro ψ s c σ u k l L hT hTa hZ hp hne _hL
  rcases traceLine_periodBound_of_tracePerpRealisable hp hne
      (tracePerpSlice_holds ψ s c σ u hT hTa hZ) with hle | hbound
  · exact le_trans inf_le_left hle
  · exact hbound

/-- **The tamed dimension bound is a theorem** (no input beyond the hypotheses of the residual). -/
theorem keyTame_holds : KeyTame :=
  keyTame_of_tracePerpSlice tracePerpSlice_holds

/-- **Pardon's Lemma 3 for the smooth tori, in general position, is a theorem**, given the general
position of the box-sphere trace. -/
theorem smoothHalfSTame_holds (hnice : Work.BoxShrink.Pinch.BoxSliceNice) : SmoothHalfSTame :=
  smoothHalfSTame_of_tracePerpSlice hnice tracePerpSlice_holds

/-- The same in the parent chapter's name: the corrected field `PushOffHalfTame` of the pinch is a
theorem. -/
theorem pushOffHalfTame_holds (hnice : Work.BoxShrink.Pinch.BoxSliceNice) :
    Work.BoxShrink.Pinch.PushOffHalfTame :=
  smoothHalfSTame_holds hnice

/-- **The residual settles the ledger's `bubble` in the corrected form**: the `bubble` field of the
ledger, as corrected in `Tamed.lean`, is Pardon's Lemma 3 conclusion. -/
theorem bubbleHalf_of_boxSliceNice (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hT : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hTa : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u)
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hS : ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ))
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u)) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  Work.BoxShrink.Pinch.smoothHalfS_of_pushOffHalfTame (pushOffHalfTame_holds hnice) hT hTa
    ψ s c σ u hS hZ

end

end Work.BoxShrink.PinchOff

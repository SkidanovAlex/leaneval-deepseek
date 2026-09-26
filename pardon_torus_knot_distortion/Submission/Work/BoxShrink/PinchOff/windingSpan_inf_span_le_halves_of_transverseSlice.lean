import Mathlib
import Submission.Work.BoxShrink.PinchOff.PerpCases
import Submission.Work.BoxShrink.PinchOff.CompactSlice
import Submission.Work.BoxShrink.PinchOff.Honest
import Submission.Work.BoxShrink.Pinch.Trace
import Submission.Work.BoxShrink.PinchOff.SliceCover

/-!
# The per-class bound of the pinch, from the box-local residual

This module proves the requested lemma

  `WindingSpan F (boxRegion F s c σ) ⊓ ℚ·(k,l) ≤ WindingSpan F (upperRegion ∪ lowerRegion)`

for every configuration whose slice is transverse and *tame* (`TransverseSlice`, `TameSlice`), whose
slice carries no essential loop (`hZ`), and every nonzero period `(k,l)` of the cutting plane's trace
(`TracePeriod`).

It is proved by reducing it to the chapter's box-local residual `TracePerpSlice`, which — this is the
point of the module — is **provable**, not open:

* `tracePerpSlice_holds` : `TracePerpSlice`.  The tameness hypothesis `TameSlice` is
  `Work.Smooth.Plane.TransversePlane` for the flat disc of the box, whose data are *finitely many*
  closed curves and arcs parametrised over the **compact** interval
  `Work.Smooth.Plane.ArcInterval`; hence `TameSlice` already *proves* `IsCompact (Sigma …)`
  (`Work.BoxShrink.PinchOff.isCompact_sliceRegion_of_tameSlice`, `SliceCover.lean`).  At a compact
  slice the chapter's circles-only theorem
  (`Work.BoxShrink.PinchOff.tracePerpRealisable_of_isCompact_slice`, `CompactSlice.lean`) gives the
  residual outright.  So the residual is *not* the "non-compact slice" obligation of the chapter's
  `CompactSlice.lean` / `Honest.lean`: with `TameSlice` as it stands, the non-compact case is empty.
* the requested lemma then follows from the residual through
  `Work.BoxShrink.PinchOff.traceLine_periodBound_of_tracePerpRealisable` (`PerpCases.lean`): either
  the box region does not drop at all, or the per-class bound holds with the class `(k,l)` itself.

Note (for the record): the two hypotheses `hTa` and `hnc` of the requested statement are *mutually
inconsistent* — `hTa` proves `IsCompact (Sigma ψ s c σ u)` while `hnc` assumes its negation — so the
statement is vacuously true as well; the proof below does not use `hnc` (nor `hL`), i.e. it proves
the statement without them.  An honest "non-compact slice" statement needs a tameness predicate
whose arcs are *open* at their endpoints; the present `TameSlice` forces compactness.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The box-local residual is a theorem.**  For a configuration with a transverse and tame slice
whose slice carries no essential loop, the factored residual `TracePerpRealisable` holds — so the
chapter's `TracePerpSlice` is *not* an open statement.

The reason: `TameSlice` is a `Work.Smooth.Plane.TransversePlane` datum, i.e. the slice is covered by
finitely many closed curves and arcs of the plane, all parametrised over the *compact* interval
`ArcInterval`; hence the slice is compact (`isCompact_sliceRegion_of_tameSlice`), and at a compact
slice the circles-only theorem of `CompactSlice.lean` supplies the residual. -/
theorem tracePerpSlice_holds : TracePerpSlice := by
  intro ψ s c σ u hT hTa hZ
  exact tracePerpRealisable_of_isCompact_slice hT
    (isCompact_sliceRegion_of_tameSlice hTa) hZ

/-- The same, at a fixed configuration, in the form used below. -/
theorem tracePerpRealisable_of_tameSlice (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hTa : Work.BoxShrink.Pinch.TameSlice ψ s c σ u)
    (hZ : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Sigma ψ s c σ u)) :
    Work.BoxShrink.Pinch.TracePerpRealisable (Work.Smooth.Morse.torus ψ) s c σ u :=
  tracePerpSlice_holds ψ s c σ u hT hTa hZ

/-- **The class of a nonzero trace period survives in the halves, modulo the box region's span**:
the per-class bound of the residual (`TracePeriodBound`) — which is the requested lemma — holds at
every transverse, tame configuration whose slice carries no essential loop. -/
theorem windingSpan_inf_span_le_halves_of_transverseSlice {ψ : Submission.Diffeo} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {k l : ℤ}
    {L : Submodule ℚ (ℚ × ℚ)}
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hTa : Work.BoxShrink.Pinch.TameSlice ψ s c σ u)
    (hnc : ¬ IsCompact (Work.BoxShrink.PinchOff.Sigma ψ s c σ u))
    (hZ : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.PinchOff.Sigma ψ s c σ u))
    (hp : Work.BoxShrink.Pinch.TracePeriod (Work.Smooth.Morse.torus ψ) c σ u k l)
    (hne : (k, l) ≠ 0)
    (hL : Work.BoxShrink.Pinch.TraceLine (Work.Smooth.Morse.torus ψ) c σ u L) :
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) ⊓
      Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) := by
  have _hnc := hnc
  have _hL := hL
  rcases traceLine_periodBound_of_tracePerpRealisable (ψ := ψ)
      hp hne (tracePerpRealisable_of_tameSlice hT hTa hZ) with hle | hbound
  · exact le_trans inf_le_left hle
  · exact hbound

end

end Work.BoxShrink.PinchOff

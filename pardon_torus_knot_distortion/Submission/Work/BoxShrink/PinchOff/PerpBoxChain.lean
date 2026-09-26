import Submission.Work.BoxShrink.PinchOff.PerpBox
import Submission.Work.BoxShrink.PinchOff.tameClosedSlice_of_tameSlice

/-!
# The box-local residual without the tameness transfer

`PerpBox.lean`'s chain from `TracePerpSliceBox` to `KeyTame`/`SmoothHalfSTame` carries the
implication `TameSlice → TameClosedSlice` as an explicit hypothesis `hhon`; the delegated lemma
`tameClosedSlice_of_tameSlice` discharges it, so the chain below has no extra hypothesis.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The box-local residual gives the tamed dimension bound** (no extra hypothesis). -/
theorem keyTame_of_tracePerpSliceBox' (h : TracePerpSliceBox) : KeyTame :=
  keyTame_of_tracePerpSliceBox
    (fun ψ s c σ u hT => tameClosedSlice_of_tameSlice ψ s c σ u hT) h

/-- **The box-local residual gives the corrected residual of the chapter.** -/
theorem smoothHalfSTame_of_tracePerpSliceBox' (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TracePerpSliceBox) : SmoothHalfSTame :=
  smoothHalfSTame_of_tracePerpSliceBox hnice
    (fun ψ s c σ u hT => tameClosedSlice_of_tameSlice ψ s c σ u hT) h

/-- The same, in the parent chapter's own name. -/
theorem pushOffHalfTame_of_tracePerpSliceBox' (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TracePerpSliceBox) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  pushOffHalfTame_of_tracePerpSliceBox hnice
    (fun ψ s c σ u hT => tameClosedSlice_of_tameSlice ψ s c σ u hT) h

/-- **End to end** without the tameness transfer. -/
theorem smoothHalfS_of_tracePerpSliceBox' (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TracePerpSliceBox)
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    Work.BoxShrink.Pinch.SmoothHalfS :=
  smoothHalfS_of_tracePerpSliceBox hnice
    (fun ψ s c σ u hT => tameClosedSlice_of_tameSlice ψ s c σ u hT) h htrans htame

end

end Work.BoxShrink.PinchOff

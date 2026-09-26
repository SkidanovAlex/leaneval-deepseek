import Submission.Work.BoxShrink.PinchOff.Extras
import Submission.Work.BoxShrink.PinchOff.equation1Input_holds
import Submission.Work.BoxShrink.Pinch.PushOffNoJump
import Submission.Work.BoxShrink.Pinch.HalfDichotomy

/-!
# Pardon's equation (1), discharged: the dichotomy at the box and at the two half-box spheres

`equation1Input_holds.lean` proves the parent chapter's carried classical input
`Work.BoxShrink.Pinch.Equation1Input`.  This module re-exports the dichotomy statements which the
parent chapter derives from it (`Work.BoxShrink.Pinch.pardonDichotomy_boxRegion_of_equation1`,
`pardonDichotomy_upperRegion_of_equation1`, `pardonDichotomy_lowerRegion_of_equation1`) **with the
input discharged**, so that a caller never has to name it.

These are the ingredients of Pardon's Lemma 2.3 (`spherefamily`):
at a nice, inessential level of the box norm the region inside the box has winding span `⊥` or `⊤`,
and the same holds for the two half-box spheres of the pinch.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The dichotomy at the box region, unconditionally** (Pardon's equation (2.1) at the initial
sphere of the pinch). -/
theorem pardonDichotomy_boxRegion {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)}
    (hnice : Work.Smooth.Morse.NiceLevel ψ (Work.BoxShrink.Pinch.boxLevel s c σ) 0)
    (hS : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) :=
  Work.BoxShrink.Pinch.pardonDichotomy_boxRegion_of_equation1 equation1Input_holds hnice hS

/-- **The dichotomy at the upper half-region, unconditionally.** -/
theorem pardonDichotomy_upperRegion {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hnice : Work.Smooth.Morse.NiceLevel ψ (Work.BoxShrink.Pinch.upperLevel s c σ u) 0)
    (htrace : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (Work.BoxShrink.Pinch.upperLevel s c σ u) 0)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
  Work.BoxShrink.Pinch.pardonDichotomy_upperRegion_of_equation1 equation1Input_holds hnice htrace

/-- **The dichotomy at the lower half-region, unconditionally.** -/
theorem pardonDichotomy_lowerRegion {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hnice : Work.Smooth.Morse.NiceLevel ψ (Work.BoxShrink.Pinch.lowerLevel s c σ u) 0)
    (htrace : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (Work.BoxShrink.Pinch.lowerLevel s c σ u) 0)) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
  Work.BoxShrink.Pinch.pardonDichotomy_lowerRegion_of_equation1 equation1Input_holds hnice htrace

/-- **Pardon's equation (1) itself, in the form of this chapter's reduction**: `SmoothHalfS`
follows from the tamed residual `Key`-free chain — recorded because the parent chapter's
`smoothHalfS_of_pinchNoJump` now needs no input beyond the box-sphere general position. -/
theorem smoothHalfS_of_pinchNoJump_boxSliceNice (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : Work.BoxShrink.Pinch.PinchNoJump) : Work.BoxShrink.Pinch.SmoothHalfS :=
  Work.BoxShrink.Pinch.smoothHalfS_of_pinchNoJump equation1Input_holds hnice h

end

end Work.BoxShrink.PinchOff

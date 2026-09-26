import Submission.Work.BoxShrink.Pinch.Defs

/-!
# The target of the pinch, in the form the deliverable allows

The assignment for this chapter allows two of Pardon's geometric inputs to be carried as
*documented hypotheses*: the transversality of the cutting plane along the slice
(`Work.BoxShrink.Pinch.TransverseSlice`) and the tameness of the slice (`TameSlice`, the classical
"finite union of arcs and circles", derived from the classification of compact `1`-manifolds).
The remaining statement — the one this chapter is asked to prove — is therefore

> for every smooth torus of the challenge, every box, every plane and every configuration whose
> slice is *transverse* and *tame*, if neither the trace of the box sphere nor the slice carries an
> essential loop, then the conclusion of Pardon's Lemma 3 holds.

That is `Work.BoxShrink.Pinch.PushOffHalfTame` below.  It is *strictly weaker* than
`Work.BoxShrink.Pinch.SmoothHalfS` (which asks for the same conclusion with no hypothesis on the
configuration beyond `hS` and `hZ`), and it is the exact statement on which the challenge's
`Work.BoxShrink.FinalInput` depends once the two geometric inputs are carried by the caller:
`smoothHalfS_of_pushOffHalfTame` turns it into `SmoothHalfS` as soon as transversality and tameness
are available for every configuration, and `pushOffHalfTame_of_smoothHalfS` shows the containment is
the only difference between the two.

The remaining mathematical content of `PushOffHalfTame` is Pardon's Lemma 3 with a *tame transverse*
slice, for which the chapter's tools are: the exact criterion of `Plane.lean`
(`not_containsEssentialLoop_of_component_windows`, `containsEssentialLoop_of_periodicPath`), on
which the slice becomes a finite union of compact arcs (with endpoints on the trace of the box
sphere) and of inessential circles, the collar of `Surfaces.lean` (`exists_collar`), and the
structural analysis of `SlicingLoops.lean` (every closed component of a tame slice has vanishing
winding) and the sharp special case of the chaining argument: the arcs of
the slice and the components of the trace of the box sphere form closed curves in the plane whose
winding vectors can be nonzero unless the two traces are arranged as in Pardon's family, which is
exactly what `hS` and `hZ` forbid.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **The push-off with a tame transverse slice**: the statement the chapter is asked to prove,
with Pardon's transversality and tameness of the slice carried as documented hypotheses. -/
def PushOffHalfTame : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    TransverseSlice ψ s c σ u → TameSlice ψ s c σ u →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Work.BoxShrink.Bubble.BubbleHalf (Work.Smooth.Morse.torus ψ) s c σ u

/-- `PushOffHalfTame` is implied by the unrestricted smooth push-off (the transversality and
tameness hypotheses are simply ignored). -/
theorem pushOffHalfTame_of_smoothHalfS (h : SmoothHalfS) : PushOffHalfTame :=
  fun ψ s c σ u _ _ hS hZ => h ψ s c σ u hS hZ

/-- **`PushOffHalfTame` gives the smooth push-off of the challenge** as soon as transversality and
tameness of the slice are available for every configuration (the two documented inputs). -/
theorem smoothHalfS_of_pushOffHalfTame (h : PushOffHalfTame)
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TameSlice ψ s c σ u) :
    SmoothHalfS :=
  fun ψ s c σ u hS hZ => h ψ s c σ u (htrans ψ s c σ u) (htame ψ s c σ u) hS hZ

end

end Work.BoxShrink.Pinch

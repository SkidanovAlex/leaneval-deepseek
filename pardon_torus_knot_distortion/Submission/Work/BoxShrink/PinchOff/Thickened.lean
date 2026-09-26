import Submission.Work.BoxShrink.PinchOff.Tamed

/-!
# The thickened (paper-faithful) form of the pinch residual

Pardon's Lemma `doublebubble2` (the form he actually applies in §4 of the paper) does **not**
conclude Pardon's Lemma 3 in the form `BubbleHalf`: it concludes that for some half `H_i` and
**every** `η > 0` the surface `F ∩ (B(η) + int(H_i))` — the `η`-neighbourhood of the half — has a
connected component of genus `g`.  He then absorbs the thickening in the box-shrinking step ("each
`H_i` is strictly contained in a congruent image of `Box(2^{-1/3}(1+ε) + ε/2)`").

In the box/plane configuration the `η`-neighbourhood of the half-region `Ω⁺` contains, for every
`η > 0`, the *closed* half `Ω ∩ {0 ≤ G}` (every point of the closed half is at distance `0` from the
open half).  So Pardon's conclusion is implied by — and in the degenerate configurations only
implied by — the statement that the two **closed** halves together carry an essential loop whenever
the box region does:

  `ClosedHalfS :  ∀ ψ s c σ u, hS → hZ → ContainsEssentialLoop Ω → ContainsEssentialLoop ClosedHalves`.

This form is *strictly weaker* than `SmoothHalfSTame`/`BubbleHalf` (`closedHalfS_of_bubbleHalf`
below), it is *not* refuted by the tangency counterexample of `KeyRefuted.lean` (there the
half-regions are inessential but the closed upper half contains the meridian `{u = 0}`, which meets
the plane only at the tangency point, so it *is* essential), and it is the form Pardon's proof
delivers.  The workspace's sibling chapter `Work.PinchLemma3` uses the same closed halves
(`closedUpper`, `closedLower`) for exactly this reason.

No proof of `ClosedHalfS` is given here; it is recorded as the *paper-faithful* target, strictly
weaker than the exact one, for a future stretch.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The upper closed half-region**: the box region on the `G ≥ 0` side of the plane. -/
def closedHalfUp (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Set R3 :=
  Omega ψ s c σ ∩ {y : R3 | 0 ≤ Work.BoxShrink.Bubble.planeCoord c σ u y}

/-- **The lower closed half-region**. -/
def closedHalfDown (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Set R3 :=
  Omega ψ s c σ ∩ {y : R3 | Work.BoxShrink.Bubble.planeCoord c σ u y ≤ 0}

/-- **The two closed half-regions together** — the thickened half of Pardon's Lemma `doublebubble2`. -/
def closedHalves (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Set R3 :=
  closedHalfUp ψ s c σ u ∪ closedHalfDown ψ s c σ u

/-- **The paper-faithful (thickened) form of the pinch residual**: if the box region carries an
essential loop, then so do the two closed half-regions together, under the two endpoint
hypotheses. -/
def ClosedHalfS : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    (surface ψ).ContainsEssentialLoop (Omega ψ s c σ) →
    (surface ψ).ContainsEssentialLoop (closedHalves ψ s c σ u)

/-- **The exact form implies the thickened form**: the closed halves contain the open ones. -/
theorem closedHalfS_of_bubbleHalf
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u) : ClosedHalfS := by
  intro ψ s c σ u hS hZ hbox
  rcases h ψ s c σ u hS hZ hbox with hup | hlo
  · refine Work.CoreTopology.ParamTorus.containsEssentialLoop_mono _ ?_ hup
    intro z hz
    refine Or.inl ⟨hz.1, ?_⟩
    have h2 : c (σ 2) + u < z (σ 2) := hz.2
    change (0 : ℝ) ≤ Work.BoxShrink.Bubble.planeCoord c σ u z
    rw [Work.BoxShrink.Bubble.planeCoord_apply]
    linarith
  · refine Work.CoreTopology.ParamTorus.containsEssentialLoop_mono _ ?_ hlo
    intro z hz
    refine Or.inr ⟨hz.1, ?_⟩
    have h2 : z (σ 2) < c (σ 2) + u := hz.2
    change Work.BoxShrink.Bubble.planeCoord c σ u z ≤ (0 : ℝ)
    rw [Work.BoxShrink.Bubble.planeCoord_apply]
    linarith

/-- The thickened residual from the corrected (tamed) one, *under the general position hypotheses*
of the tamed residual.  Without them the implication is not available: the corrected residual
`SmoothHalfSTame` is stated for transverse tame slices only, and the abstract form `ClosedHalfS`
carries no such hypothesis. -/
theorem closedHalfS_of_smoothHalfSTame
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u)
    (h : SmoothHalfSTame) : ClosedHalfS :=
  closedHalfS_of_bubbleHalf fun ψ s c σ u hS hZ =>
    h ψ s c σ u (htrans ψ s c σ u) (htame ψ s c σ u) hS hZ

end

end Work.BoxShrink.PinchOff

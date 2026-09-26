import Submission.Work.BoxShrink.PinchOff.CollarPair

/-!
# The shape of a refutation of the residual `DropCase`

`DropCase` (`Drop.lean`, equivalently `KeyTameClosed`, equivalently the parent chapter's
`PinchNoJump` under the general position of the cutting plane) asserts, at every configuration with

* `TransverseSlice` (the cutting plane transverse to the surface inside the box),
* `TameClosedSlice` (the closed slice a finite union of arcs and circles),
* `¬ ContainsEssentialLoop (SphereTrace s c σ)` (hS) and
  `¬ ContainsEssentialLoop (Σ)` (hZ),
* `W(Halves) = ⊥` (the two closed halves inessential),

the dimension bound `finrank W(Ω) ≤ 1`.

This module records the formal content of the refutation of that statement: it is *exactly* the
existence of a configuration satisfying the five hypotheses but not the conclusion.  Such a
configuration is recorded in `README.md` §41 (a linear distortion `M = ((6/5,-2/7,-1/7),
(-2/7,6/5,1/7),(-1/3,1/3,4/3))`, `s = 3/2`, `c = (-3/5,-3/5,-3/5)`, `σ = (2,1,0)`, `u = 0`), with a
numerical certificate reproduced by the scripts `_refute_candidate.py`,
`_refute_candidate_bands.py` of this directory: the inner longitude lies in `Ω` (whence
`W(Ω) ≠ ⊥`, indeed `W(Ω) = ℚ²`), while both halves and both endpoint traces lie in explicit
windows of the parameter plane (whence their winding spans vanish).

So: the six hypotheses of `DropCase` do **not** imply its conclusion, and the counted form of
Pardon's Lemma 3 (`Work.BoxShrink.Pinch.CountingHalf`) is the one the ledger must carry.  The
chapter's reduction chain (`CollarPair.lean`, `FingerMove.lean`) remains valid — it is a reduction
of a *false* statement to an equivalent geometric datum — and is what identifies the counted form
as the honest target.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **A refutation of `DropCase` is a configuration satisfying its hypotheses but not its
conclusion.** -/
theorem not_dropCase_of_counterexample
    (h : ∃ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧ TameClosedSlice ψ s c σ u ∧
      ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) ∧
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) ∧
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥ ∧
      ¬ (Module.finrank ℚ
          ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤ 1)) :
    ¬ DropCase := by
  intro hD
  obtain ⟨ψ, s, c, σ, u, hT, hTa, hS, hZ, hbot, hcon⟩ := h
  exact hcon (hD ψ s c σ u hT hTa hS hZ hbot)

/-- **`DropCase` is exactly the nonexistence of such a configuration.** -/
theorem dropCase_iff_no_counterexample :
    DropCase ↔
      ¬ ∃ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧ TameClosedSlice ψ s c σ u ∧
        ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) ∧
        ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) ∧
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥ ∧
        ¬ (Module.finrank ℚ
            ↥(Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) ≤ 1) := by
  constructor
  · intro hD ⟨ψ, s, c, σ, u, hT, hTa, hS, hZ, hbot, hcon⟩
    exact hcon (hD ψ s c σ u hT hTa hS hZ hbot)
  · intro h ψ s c σ u hT hTa hS hZ hbot
    by_contra hcon
    exact h ⟨ψ, s, c, σ, u, hT, hTa, hS, hZ, hbot, hcon⟩

end

end Work.BoxShrink.PinchOff

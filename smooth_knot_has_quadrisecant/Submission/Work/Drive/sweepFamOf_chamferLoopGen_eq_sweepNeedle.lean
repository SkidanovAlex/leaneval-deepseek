import Mathlib
import Submission.Work.Drive.chamferLoopGenBlur
import Submission.Work.Drive.chamferSchedule
import Submission.Work.Drive.sweepFamOf

namespace Work.Drive

/-!
# The blurred scheduled slice at the trough is the needle

`Work.Drive.sweepNeedleFam r D lam δ₁ δ₂ ε` is the blurred slice `sweepFam r D lam δ₁ δ₂ ε` of the
*standard* chamfered loop (`sweepNeedleFam` is by definition the `ε`-slice of `sweepFam`), while the
endgame of the uniform-`ρ₀` design runs the *scheduled* loop
`Γ = chamferLoopGen r D lay (schedAlpha …) (schedBeta …)`.  The two agree at `σ = ε` as soon as the
schedule is still in its bottom trough on the whole blur window `[ε - δ₂, ε + δ₂]`: there the
scheduled loop *is* the ordinary chamfered loop
(`sweepFamOf_chamferLoopGen_eq_sweepFam`, `Drive/chamferLoopGenBlur.lean`).

This is the `htop` conversion that lets the top end state its endpoint as `sweepNeedleFam`.
-/

open LeanEval.KnotTheory.Quadrisecant

/-- **The blurred scheduled slice at a trough is the needle.** -/
theorem sweepFamOf_chamferLoopGen_eq_sweepNeedle {r : ℝ → Space} {d : BandArcData}
    (D : SweepData d) {ρ₀ δs cQ lay δ₁ δ₂ ε : ℝ}
    (htrough : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      schedAlpha lay ρ₀ δs D (ε - δ₂ * v) = lay ∧
      schedBeta r lay ρ₀ δs cQ D (ε - δ₂ * v) = lay) :
    sweepFamOf
        (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D))
        δ₁ δ₂ ε
      = sweepNeedleFam r D lay δ₁ δ₂ ε := by
  have h := sweepFamOf_chamferLoopGen_eq_sweepFam (r := r) (D := D) (lay := lay)
    (α := schedAlpha lay ρ₀ δs D) (β := schedBeta r lay ρ₀ δs cQ D)
    (σ := ε) (δ₁ := δ₁) (δ₂ := δ₂) htrough
  exact h

end Work.Drive

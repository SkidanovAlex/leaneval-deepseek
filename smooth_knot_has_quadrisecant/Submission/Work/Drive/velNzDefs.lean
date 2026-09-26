import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs

/-!
# The averaged forward chord of the raw chamfered sweep loop

`Work.Drive.avgChord r D lam δ₁ δ₂ σ n t g` is the `(v,u)`-average, with the smoothing bump
`Work.Drive.sweepBump` as weight, of the `n`-component of the forward chord
`Γ(s_v, t+g-δ₁u) − Γ(s_v, t-δ₁u)` of the raw chamfered sweep loop `Γ = sweepLoopChamfer`,
over `s_v = σ - δ₂ v`.

It is the single quantity in which both halves of `Work.Drive.sweepFamVelNz` are stated:

* the *analytic* half (proved in `Submission/Work/Drive/sweepFamVelNz.lean`) identifies
  `⟪n, Φ_σ(t+g) − Φ_σ(t)⟫` (`Φ_σ = sweepFam r D lam δ₁ δ₂ σ`) with `avgChord ... t g`;
* the *geometric* half (`Work.Drive.sweepFamVelGeom`, in
  `Submission/Work/Drive/sweepFamVelGeom.lean`) produces `n ≠ 0` and `c > 0` with
  `c * g ≤ avgChord ... t g` for all small `g > 0`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-- The `(v,u)`-averaged forward chord of the raw chamfered sweep loop in the direction `n`. -/
def avgChord (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ : ℝ) (σ : ℝ) (n : Space) (t g : ℝ) : ℝ :=
  ∫ v in (-1 : ℝ)..1, sweepBump v *
    (∫ u in (-1 : ℝ)..1, sweepBump u *
      inner ℝ n (sweepLoopChamfer r D lam (σ - δ₂ * v) (t + g - δ₁ * u)
        - sweepLoopChamfer r D lam (σ - δ₂ * v) (t - δ₁ * u)))

end Work.Drive

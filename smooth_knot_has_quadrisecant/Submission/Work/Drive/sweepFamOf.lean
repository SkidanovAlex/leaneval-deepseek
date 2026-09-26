import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.velNzDefs

/-!
# The double bump-blur of an arbitrary continuous loop family

`Work.Drive.sweepFam r D lam δ₁ δ₂` (`Submission/Work/Drive/chordSweepSmooth.lean`) is the double
convolution of the *chamfered* sweep loop with the smooth bump `sweepBump`:

`sweepFam r D lam δ₁ δ₂ σ t = ∫ v in (-1)..1, sweepBump v • ∫ u in (-1)..1, sweepBump u •
sweepLoopChamfer r D lam (σ - δ₂ v) (t - δ₁ u)`.

The `OFat` lane of the project needs the same construction for the *perpendicular-chamfer* loop
`Work.Drive.thinLoop` (`Submission/Work/Drive/thinLoopSeparation.lean`), whose slices are injective
on one period for a different reason.  Rather than duplicating the analytic layer, this module
isolates the construction from the loop: `sweepFamOf Γ δ₁ δ₂` is the double blur of an arbitrary
continuous, `period`-periodic family `Γ`.

* `Work.Drive.sweepFamOf` — the definition;
* `Work.Drive.sweepFam_eq_sweepFamOf` — `sweepFam` is the special case `Γ = sweepLoopChamfer`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The double bump-blur of a loop family.**  Convolution in the loop parameter (width `δ₁`) and
in the sweep parameter (width `δ₂`) with the smooth bump `Work.Drive.sweepBump`. -/
def sweepFamOf (Γ : ℝ → ℝ → Space) (δ₁ δ₂ : ℝ) (s t : ℝ) : Space :=
  ∫ v in (-1)..1, sweepBump v •
    (∫ u in (-1)..1, sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u))

/-- **The average chord of a loop family over the blur box.**  For a loop `Γ`, the box
`[s-δ₂, s+δ₂] × [t-δ₁, t+δ₁]` and a direction `n`, this is
`∫∫ b(v) b(u) ⟪n, Γ (s-δ₂v) (t+g-δ₁u) - Γ (s-δ₂v) (t-δ₁u)⟫`, i.e. the average over the box of the
`n`-pairing of the *chord* of length `g` of the loop.  Its positivity is the local injectivity of
the blurred slice; `Work.Drive.avgChord` is the special case `Γ = sweepLoopChamfer r D lam`. -/
def avgChordOf (Γ : ℝ → ℝ → Space) (δ₁ δ₂ : ℝ) (s : ℝ) (n : Space) (t g : ℝ) : ℝ :=
  ∫ v in (-1)..1, sweepBump v *
    (∫ u in (-1)..1, sweepBump u *
      inner ℝ n (Γ (s - δ₂ * v) (t + g - δ₁ * u) - Γ (s - δ₂ * v) (t - δ₁ * u)))

/-- **`avgChord` is `avgChordOf`.** -/
theorem avgChord_eq_avgChordOf (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ σ : ℝ) (n : Space) (t g : ℝ) :
    avgChord r D lam δ₁ δ₂ σ n t g
      = avgChordOf (sweepLoopChamfer r D lam) δ₁ δ₂ σ n t g := rfl

/-- **`sweepFam` is `sweepFamOf`.**  The existing doubly smoothed sweep family is the double blur of
the chamfered loop. -/
theorem sweepFam_eq_sweepFamOf (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ : ℝ) :
    sweepFam r D lam δ₁ δ₂ = sweepFamOf (sweepLoopChamfer r D lam) δ₁ δ₂ := rfl

end Work.Drive

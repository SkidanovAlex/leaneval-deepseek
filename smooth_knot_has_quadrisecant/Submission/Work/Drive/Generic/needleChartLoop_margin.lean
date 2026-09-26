import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.Generic.nclmWiring
import Submission.Work.Drive.Generic.nclmChartDataE

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant

/-- **The per-loop angular-velocity margin of the needle's chart.**  For a knot without inflections
and a band arc avoiding the trisecant set `O`, the numerator of every individual chamfered loop of
the blur window about the *needle's* chart centre `Work.Drive.chartC` — taken in the needle's chart
frame `(chartE, v)` — is bounded below by a positive constant `κ`, uniformly over the box and over
the loop parameter.  This is the geometric heart of the needle's angular-velocity pin
(`Work.Drive.NeedleShiftedAngVelDep`): the centre `chartC` lies in the interior of the convex lens
bounded by each loop, so each loop turns counterclockwise about it with a definite margin. -/
theorem needleChartLoop_margin {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : Work.Drive.SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ Λ : ℝ, 0 < Λ ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      ∀ (v : Space), ‖v‖ = 1 →
        Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
          = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        ∀ (σ s : ℝ), ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          κ ≤ inner ℝ (Work.Drive.sweepLoopChamfer r D lam σ s
                  - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
              * inner ℝ (Work.Drive.chamferVel r D lam σ s) v
            - inner ℝ (Work.Drive.sweepLoopChamfer r D lam σ s
                  - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
              * inner ℝ (Work.Drive.chamferVel r D lam σ s)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v) := by
  exact nclm_margin_of_chartDataC hr hinfl D (nclm_chartDataE hr hinfl D)

end Work.Drive.Generic

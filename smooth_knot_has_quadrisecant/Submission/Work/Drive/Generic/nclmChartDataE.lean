import Submission.Work.Drive.Generic.nclmCompose
import Submission.Work.Drive.Generic.nclm_clauseScale
import Submission.Work.Drive.Generic.nclm_clauseProfile
import Submission.Work.Drive.Generic.nclm_clauseEndpoints
import Submission.Work.Drive.Generic.nclm_clauseChamfer
import Submission.Work.Drive.Generic.nclm_clauseConcave

/-!
# The chart-data package `nclmDataC` from the five clause packages

This is the second (package-based) producer of the chart data
`Work.Drive.Generic.nclmDataC`: it combines the five proved clause packages
(`nclm_clauseScale`, `nclm_clauseProfile`, `nclm_clauseEndpoints`, `nclm_clauseChamfer`,
`nclm_clauseConcave`) through the assembly `Work.Drive.Generic.nclm_dataC_of_packages`.  It gives the
same statement as `Work.Drive.Generic.nclm_chartDataC`, hence (with
`Work.Drive.Generic.nclm_margin_of_chartDataC`) the per-loop margin
`Work.Drive.Generic.needleChartLoop_margin`.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant

/-- **The chart data, from the clause packages.** -/
theorem nclm_chartDataE {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (cℓ Cℓ ch Ch cm cE cK Λ : ℝ),
        0 < cℓ ∧ 0 < Cℓ ∧ 0 < ch ∧ 0 < Ch ∧ 0 < cm ∧ 0 < cE ∧ 0 ≤ cK ∧ 0 < Λ ∧
        ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ (v : Space), ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
          nclmDataC r D lam δ₁ δ₂ ε v cℓ Cℓ ch Ch cm cE cK :=
  nclm_dataC_of_packages hr D (nclm_clauseScale hr hinfl D) (nclm_clauseProfile hr hinfl D)
    (nclm_clauseEndpoints hr hinfl D) (nclm_clauseChamfer hr hinfl D) (nclm_clauseConcave hr hinfl D)

end Work.Drive.Generic

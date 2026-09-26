import Submission.Work.Drive.AB.pinSetup

/-!
# The two analytic obligations of the needle's angular-velocity pin, as `Prop`s

`Work.Drive.ChartLoopMargin` is the *per-loop margin* (the geometric heart, the conclusion of
`Work.Drive.Generic.needleChartLoop_margin`) and `Work.Drive.ChartOscBounds` the *oscillation bound*
of the loop coordinates over the blur window (the conclusion of
`Work.Drive.Generic.needleChart_oscBounds`).  The bodies are copied verbatim from those two
statements, so a proof of either statement can be passed directly where the corresponding `Prop` is
expected.

The module `Submission/Work/Drive/AB/pinReduction.lean` assembles them into
`Work.Drive.NeedleShiftedAngVelDep` via `Work.Drive.needle_num_pos_of_diag_osc`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-- **The per-loop angular-velocity margin of the needle's chart** (see
`Work.Drive.Generic.needleChartLoop_margin`). -/
def ChartLoopMargin (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ Λ : ℝ, 0 < Λ ∧ ∃ κ : ℝ, 0 < κ ∧
    ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
      0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
    ∀ (v : Space), ‖v‖ = 1 →
      chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
        = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v →
      ∀ (σ s : ℝ), ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        κ ≤ inner ℝ (sweepLoopChamfer r D lam σ s - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)
            * inner ℝ (chamferVel r D lam σ s) v
          - inner ℝ (sweepLoopChamfer r D lam σ s - chartC r D lam δ₁ δ₂ ε v) v
            * inner ℝ (chamferVel r D lam σ s) (chartE r D lam δ₁ δ₂ ε v)

/-- **The oscillation bounds of the loop coordinates over the blur window** (see
`Work.Drive.Generic.needleChart_oscBounds`). -/
def ChartOscBounds (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ κ : ℝ, 0 < κ → ∃ Λ : ℝ, 0 < Λ ∧
    ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
      0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
    ∀ (v : Space), ‖v‖ = 1 →
      chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
        = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v →
      ∃ (A B A' B' : ℝ), 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ A' ∧ 0 ≤ B' ∧
        2 * (A * B') + 2 * (B * A') < κ ∧
        (∀ t : ℝ, ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₁ : ℝ, v₁ ∈ Set.Icc (-1 : ℝ) 1 →
          ∀ u' : ℝ, u' ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₂ : ℝ, v₂ ∈ Set.Icc (-1 : ℝ) 1 →
          |inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₁)
                (t + period / 4 - δ₁ * u) - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)
            - inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₂)
                (t + period / 4 - δ₁ * u') - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)| ≤ A) ∧
        (∀ t : ℝ, ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₁ : ℝ, v₁ ∈ Set.Icc (-1 : ℝ) 1 →
          ∀ u' : ℝ, u' ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₂ : ℝ, v₂ ∈ Set.Icc (-1 : ℝ) 1 →
          |inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₁)
                (t + period / 4 - δ₁ * u) - chartC r D lam δ₁ δ₂ ε v) v
            - inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₂)
                (t + period / 4 - δ₁ * u') - chartC r D lam δ₁ δ₂ ε v) v| ≤ B) ∧
        (∀ t : ℝ, ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₁ : ℝ, v₁ ∈ Set.Icc (-1 : ℝ) 1 →
          ∀ u' : ℝ, u' ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₂ : ℝ, v₂ ∈ Set.Icc (-1 : ℝ) 1 →
          |inner ℝ (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u))
              (chartE r D lam δ₁ δ₂ ε v)
            - inner ℝ (chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u'))
              (chartE r D lam δ₁ δ₂ ε v)| ≤ A') ∧
        (∀ t : ℝ, ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₁ : ℝ, v₁ ∈ Set.Icc (-1 : ℝ) 1 →
          ∀ u' : ℝ, u' ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₂ : ℝ, v₂ ∈ Set.Icc (-1 : ℝ) 1 →
          |inner ℝ (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)) v
            - inner ℝ (chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')) v| ≤ B')

end Work.Drive

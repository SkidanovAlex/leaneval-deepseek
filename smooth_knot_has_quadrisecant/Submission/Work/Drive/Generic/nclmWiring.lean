import Mathlib
import Submission.Work.Drive.Generic.nclmMain
import Submission.Work.Drive.AB.pinBounds

/-!
# The per-loop margin from the uniform chart data

`Work.Drive.Generic.nclm_assemblyC` produces the per-loop angular-velocity margin at a fixed box from
the chart data `nclmDataC` with *explicit* constants, and the explicit value

    κ = min (ch·cm·W³/(1024·period)) (min (3·cℓ·ch·W³/(16·period)) (cℓ·cE·W³/(64·period))),
    W = sweepW' D ε,

of the bound.  This module performs the quantifier bookkeeping of
`Work.Drive.Generic.needleChartLoop_margin`: the target has `Λ` and `κ` quantified *before* the box
`(lam, δ₁, δ₂)`, so the constants of the chart data must be uniform in the box — which is exactly the
statement of `Work.Drive.Generic.nclm_chartDataC`.  The margin itself is written with the *unfolded*
expression of `nclmMarg`, so that the final step of `needleChartLoop_margin` is a direct application.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant

/-- **The per-loop margin from the uniform chart data.**  From the uniform constants of
`nclm_chartDataC` (chosen per `ε`, before the box), the margin of the needle's chart loops is bounded
below by the explicit positive constant `κ` of `nclm_assemblyC`. -/
theorem nclm_margin_of_chartDataC {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : Work.Drive.SweepData d)
    (hdata : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (cℓ Cℓ ch Ch cm cE cK Λ : ℝ),
        0 < cℓ ∧ 0 < Cℓ ∧ 0 < ch ∧ 0 < Ch ∧ 0 < cm ∧ 0 < cE ∧ 0 ≤ cK ∧ 0 < Λ ∧
        ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ (v : Space), ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
          nclmDataC r D lam δ₁ δ₂ ε v cℓ Cℓ ch Ch cm cE cK) :
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
  obtain ⟨ε₀, hε₀, H⟩ := hdata
  have hp : (0 : ℝ) < period := period_pos
  refine ⟨min ε₀ (1 / 4), lt_min hε₀ (by norm_num), fun ε hε hεε₀ => ?_⟩
  have hεε₀' : ε ≤ ε₀ := le_trans hεε₀ (min_le_left _ _)
  have hε4 : ε ≤ 1 / 4 := le_trans hεε₀ (min_le_right _ _)
  obtain ⟨cℓ, Cℓ, ch, Ch, cm, cE, cK, Λ, hcℓ, hCℓ, hch, hCh, hcm, hcE, hcK, hΛ, Hbox⟩ :=
    H ε hε hεε₀'
  have hWpos : 0 < Work.Drive.sweepW' D ε :=
    nclm_window_wpos D (δ₂ := ε / 4) (ε := ε) (σ := ε) (by linarith) (by linarith) hε
      (by linarith [hε4]) (by linarith) (by linarith)
  refine ⟨min (min Λ (1 / 4)) (period / 16),
    lt_min (lt_min hΛ (by norm_num)) (div_pos hp (by norm_num)),
    min (ch * cm * (Work.Drive.sweepW' D ε) ^ 3 / (1024 * period))
      (min (3 * cℓ * ch * (Work.Drive.sweepW' D ε) ^ 3 / (16 * period))
        (cℓ * cE * (Work.Drive.sweepW' D ε) ^ 3 / (64 * period))),
    lt_min (by positivity) (lt_min (by positivity) (by positivity)), ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam2 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
  have hlamΛ' : lam ≤ Λ := le_trans hlamΛ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hlam4 : lam ≤ 1 / 4 := le_trans hlamΛ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₁Λ' : δ₁ ≤ Λ := le_trans hδ₁Λ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₁16 : δ₁ ≤ period / 16 := le_trans hδ₁Λ (min_le_right _ _)
  have hδ₂Λ' : δ₂ ≤ Λ := le_trans hδ₂Λ (le_trans (min_le_left _ _) (min_le_left _ _))
  intro v hv hb
  have hbox := Hbox lam δ₁ δ₂ hlam0 hlamΛ' hlam2 hδ₁0 hδ₁Λ' hδ₂0 hδ₂Λ' hδ₂ε v hv hb
  have hmain := nclm_assemblyC hr D hlam0 hlam2 hlam4 hδ₁0 hδ₁16 hδ₂0 hv
    hcℓ hCℓ hch hCh hcm hcE hcK hbox
  exact fun σ s hσlo hσhi => hmain.2 σ s hσlo hσhi

/-- **`Work.Drive.ChartLoopMargin` from the uniform chart data.**  The per-loop margin
`Work.Drive.ChartLoopMargin` (the hypothesis of the angular-velocity assembly
`Work.Drive.needleShiftedAngVelDep_of_bounds`) is the statement of
`Work.Drive.Generic.needleChartLoop_margin` without its (unused) band-arc hypothesis, so it follows
directly from the uniform chart data. -/
theorem chartLoopMargin_of_chartDataC {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : BandArcData} (D : Work.Drive.SweepData d)
    (hdata : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (cℓ Cℓ ch Ch cm cE cK Λ : ℝ),
        0 < cℓ ∧ 0 < Cℓ ∧ 0 < ch ∧ 0 < Ch ∧ 0 < cm ∧ 0 < cE ∧ 0 ≤ cK ∧ 0 < Λ ∧
        ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ (v : Space), ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
          nclmDataC r D lam δ₁ δ₂ ε v cℓ Cℓ ch Ch cm cE cK) :
    Work.Drive.ChartLoopMargin r D :=
  nclm_margin_of_chartDataC hr hinfl D hdata

end Work.Drive.Generic

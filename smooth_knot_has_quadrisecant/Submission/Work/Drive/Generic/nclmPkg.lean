import Mathlib
import Submission.Work.Drive.Generic.nclmData

/-!
# The clause packages of the needle's chart data

`Work.Drive.Generic.nclmDataC` collects the 21 quantitative clauses of the needle's chart at a fixed
box `(lam, δ₁, δ₂, ε)` with explicit constants.  This module splits them into four *packages*, each
of which is stated with its own ε-level constants and its own smallness threshold `Λ` — so that each
package can be proved independently of the others — together with the composition
`Work.Drive.Generic.nclm_dataC_of_packages` that reassembles `nclmDataC` from the four packages.

The packages:

* `nclmPkgScale` — the scale clauses: the window `w(ε)/2 ≤ w(σ) ≤ 2 w(ε)`, the chord-length bounds
  `cℓ·W ≤ ℓ ≤ Cℓ·W`, the facts `‖chartE‖ = 1`, `⟪chartE, v⟫ = 0`, and the height bounds
  `ch·W² ≤ ‖chartUp‖/2 ≤ Ch·W²`;
* `nclmPkgProfile` — the profile clauses: the tangent pairing `cm/4 ≤ ⟪r'(x),v⟫`, the strict
  monotonicity of the abscissa `X̃` and its derivative bounds, and the crossing point `ξ₀` with
  `ch·W² ≤ H̃ ξ₀`;
* `nclmPkgEndpoints` — the positional clauses: `|H̃| ≤ 2‖chartUp‖` on the arc and the twelve
  inequalities of the endpoint package;
* `nclmPkgChamfer` — the chamfer clauses: the acceleration sign `⟪r''(x), chatE⟫ ≤ -cE`, the two
  deviation bounds with `cE` and `cK`, and the bookkeeping `4 h₀ cK ≤ ℓ cE / 8`.

All four are stated so that their clauses are *monotone* in their constants (decreasing `cℓ`, `ch`,
`cm`, `cE`, `cK` and increasing `Cℓ`, `Ch` preserves them), which is what makes the composition a
matter of taking `min`s and `max`es.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant

/-- **The scale package** of the chart data. -/
def nclmPkgScale (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ (cℓ Cℓ ch Ch Λ : ℝ), 0 < cℓ ∧ 0 < Cℓ ∧ 0 < ch ∧ 0 < Ch ∧ 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      ∀ (v : Space), ‖v‖ = 1 →
        Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
          = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          Work.Drive.sweepW' D ε / 2 ≤ Work.Drive.sweepW' D σ
            ∧ Work.Drive.sweepW' D σ ≤ 2 * Work.Drive.sweepW' D ε) ∧
        0 < ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ ∧
        cℓ * Work.Drive.sweepW' D ε
          ≤ ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ ∧
        ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖
          ≤ Cℓ * Work.Drive.sweepW' D ε ∧
        ‖Work.Drive.chartE r D lam δ₁ δ₂ ε v‖ = 1 ∧
        inner ℝ (Work.Drive.chartE r D lam δ₁ δ₂ ε v) v = 0 ∧
        ch * Work.Drive.sweepW' D ε ^ 2 ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 ∧
        ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 ≤ Ch * Work.Drive.sweepW' D ε ^ 2

/-- **The profile package** of the chart data. -/
def nclmPkgProfile (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ (cm ch Λ : ℝ), 0 < cm ∧ 0 < ch ∧ 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      ∀ (v : Space), ‖v‖ = 1 →
        Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
          = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
            cm / 4 ≤ inner ℝ (velocity r x) v) ∧
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc (0 : ℝ) 1)) ∧
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ) ∧
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo lam (1 - lam),
          cm * Work.Drive.sweepW' D σ / 8 ≤ deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ) ∧
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ∃ ξ₀ ∈ Set.Ioo lam (1 - lam),
            nclmAX r D lam δ₁ δ₂ ε σ v ξ₀ = 0
              ∧ ch * Work.Drive.sweepW' D ε ^ 2
                ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀)

/-- **The endpoint package** of the chart data. -/
def nclmPkgEndpoints (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      ∀ (v : Space), ‖v‖ = 1 →
        Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
          = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ∀ ξ ∈ Set.Icc lam (1 - lam),
            |nclmAH r D lam δ₁ δ₂ ε σ v ξ| ≤ 2 * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖) ∧
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
            ≤ nclmAX r D lam δ₁ δ₂ ε σ v (1 - lam)
          ∧ nclmAX r D lam δ₁ δ₂ ε σ v lam
            ≤ -(‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4)
          ∧ |inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v|
            ≤ 3 * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
          ∧ |inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v|
            ≤ 3 * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
          ∧ inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
              (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
            ≤ -(‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 4)
          ∧ inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
              (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
            ≤ -(‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 4)
          ∧ 3 * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
            ≤ inner ℝ (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)) v
          ∧ |inner ℝ (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))
              (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
            ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 16
          ∧ inner ℝ (Work.Drive.sweepChord' r D σ lam
                - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
            ≤ -(‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4)
          ∧ ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ / 4
            ≤ inner ℝ (Work.Drive.sweepChord' r D σ (1 - lam)
                - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
          ∧ |inner ℝ (Work.Drive.sweepChord' r D σ lam
                - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
            ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖
          ∧ |inner ℝ (Work.Drive.sweepChord' r D σ (1 - lam)
                - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
            ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖)

/-- **The chamfer package** of the chart data. -/
def nclmPkgChamfer (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ (cE cK Λ : ℝ), 0 < cE ∧ 0 ≤ cK ∧ 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      ∀ (v : Space), ‖v‖ = 1 →
        Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
          = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
            inner ℝ (deriv (deriv r) x) (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ≤ -cE) ∧
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * cE
              ≤ inner ℝ (Work.Drive.loopDev r D σ (1 - lam))
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ∧
            lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * cE
              ≤ inner ℝ (Work.Drive.loopDev r D σ lam)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ∧
            |inner ℝ (Work.Drive.loopDev r D σ (1 - lam)) v|
              ≤ lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * cK ∧
            |inner ℝ (Work.Drive.loopDev r D σ lam) v|
              ≤ lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * cK) ∧
        4 * (‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2) * cK
          ≤ ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ * cE / 8

/-- **The chord-concavity package** of the chart data: the profile `H̃` is concave in the chord
coordinate `X̃`. -/
def nclmPkgConcave (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      ∀ (v : Space), ‖v‖ = 1 →
        Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
          = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ∀ ξ₁ ∈ Set.Icc (0 : ℝ) 1, ∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
            ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
              nclmAX r D lam δ₁ δ₂ ε σ v ξ
                  = t * nclmAX r D lam δ₁ δ₂ ε σ v ξ₁
                    + (1 - t) * nclmAX r D lam δ₁ δ₂ ε σ v ξ₂ →
              t * nclmAH r D lam δ₁ δ₂ ε σ v ξ₁
                  + (1 - t) * nclmAH r D lam δ₁ δ₂ ε σ v ξ₂
                ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ)

end Work.Drive.Generic

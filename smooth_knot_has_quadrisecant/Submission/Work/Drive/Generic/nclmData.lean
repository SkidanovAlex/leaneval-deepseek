import Mathlib
import Submission.Work.Drive.Generic.nclmBranch

/-!
# The chart-data package of the needle's loops

`Work.Drive.Generic.nclmData r D lam δ₁ δ₂ ε v` is the complete list of quantitative facts about the
needle's chart that the four branch bounds of `nclmBranch.lean` consume, at a *fixed* box
`(lam, δ₁, δ₂, ε)` and chord direction `v`.

The constants are produced *inside* the datum (they are the curvature scale of the knot at the
collapsed end, the speed at the collapsed end, and the width `sweepW' D ε` of the retained arc), so
the datum is exactly the "geometric data at scale `ε`" and its producer is a pure smallness
argument.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- **The chart data of the needle's loops.**  Writing `W := sweepW' D ε`,
`ℓ := ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖` and `h₀ := ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2`, the
datum says:

* the width of the window is comparable to `W`, and the chord length to `cℓ * W` and `Cℓ * W`;
* the height `h₀` of the chart is comparable to `ch * W²` and `Ch * W²`;
* the chart direction `chartE` is a unit vector orthogonal to `v`, and the acceleration along it is
  at most `-cE` on every retained arc of the window;
* the tangent pairs positively with `v` on every retained arc (at least `cm / 4`);
* the arc profile `ξ ↦ (X̃ ξ, H̃ ξ)` has a strictly increasing abscissa with derivative at least
  `cm * w(σ) / 8`, is chord-concave, and crosses the vertical through the centre at a point of height
  at least `ch * W²`;
* the height stays between `-2 Ch W²` and `2 Ch W²` along the arc;
* the endpoints of the arc, of the chord, and of the loop's chord vector satisfy the eight
  inequalities consumed by the chord piece;
* the two chamfer deviations satisfy the bounds consumed by the chamfer pieces, together with the
  smallness `2 h₀ cK ≤ ℓ cE / 8` that makes the chamfer bound positive.
-/
def nclmData (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) (v : Space) : Prop :=
  ∃ cℓ Cℓ ch Ch cm cE cK : ℝ,
    0 < cℓ ∧ 0 < Cℓ ∧ 0 < ch ∧ 0 < Ch ∧ 0 < cm ∧ 0 < cE ∧ 0 ≤ cK ∧
    0 < Work.Drive.sweepW' D ε ∧
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
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        cm / 4 ≤ inner ℝ (velocity r x) v) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        inner ℝ (deriv (deriv r) x) (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ≤ -cE) ∧
    ch * Work.Drive.sweepW' D ε ^ 2 ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 ∧
    ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 ≤ Ch * Work.Drive.sweepW' D ε ^ 2 ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc (0 : ℝ) 1)) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo lam (1 - lam),
      cm * Work.Drive.sweepW' D σ / 8 ≤ deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ (nclmAH r D lam δ₁ δ₂ ε σ v) ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ ξ₁ ∈ Set.Icc (0 : ℝ) 1, ∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
          nclmAX r D lam δ₁ δ₂ ε σ v ξ
              = t * nclmAX r D lam δ₁ δ₂ ε σ v ξ₁
                + (1 - t) * nclmAX r D lam δ₁ δ₂ ε σ v ξ₂ →
          t * nclmAH r D lam δ₁ δ₂ ε σ v ξ₁
              + (1 - t) * nclmAH r D lam δ₁ δ₂ ε σ v ξ₂
            ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∃ ξ₀ ∈ Set.Ioo lam (1 - lam),
        nclmAX r D lam δ₁ δ₂ ε σ v ξ₀ = 0
          ∧ ch * Work.Drive.sweepW' D ε ^ 2
            ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Icc lam (1 - lam),
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
        ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖) ∧
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

/-- **The chart data of the needle's loops, with the constants made explicit.**  This is exactly the
body of `nclmData` with the seven scale constants `cℓ Cℓ ch Ch cm cE cK` (the chord-length bounds,
the chart height bounds, the tangent speed and the acceleration/third-order bounds) as *parameters*
rather than as existentials.

It is the form in which the data can be used with *uniform* constants: the producer
(`Work.Drive.Generic.nclm_chartDataC`) can supply constants that depend only on the knot and on `ε`,
and then the per-loop margin of `Work.Drive.Generic.needleChartLoop_margin` — whose `κ` is quantified
*before* the box — follows from `Work.Drive.Generic.nclm_assemblyC`. -/
def nclmDataC (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) (v : Space) (cℓ Cℓ ch Ch cm cE cK : ℝ) : Prop :=
    0 < Work.Drive.sweepW' D ε ∧
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
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        cm / 4 ≤ inner ℝ (velocity r x) v) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        inner ℝ (deriv (deriv r) x) (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ≤ -cE) ∧
    ch * Work.Drive.sweepW' D ε ^ 2 ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 ∧
    ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 ≤ Ch * Work.Drive.sweepW' D ε ^ 2 ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc (0 : ℝ) 1)) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo lam (1 - lam),
      cm * Work.Drive.sweepW' D σ / 8 ≤ deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ (nclmAH r D lam δ₁ δ₂ ε σ v) ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ ξ₁ ∈ Set.Icc (0 : ℝ) 1, ∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
          nclmAX r D lam δ₁ δ₂ ε σ v ξ
              = t * nclmAX r D lam δ₁ δ₂ ε σ v ξ₁
                + (1 - t) * nclmAX r D lam δ₁ δ₂ ε σ v ξ₂ →
          t * nclmAH r D lam δ₁ δ₂ ε σ v ξ₁
              + (1 - t) * nclmAH r D lam δ₁ δ₂ ε σ v ξ₂
            ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∃ ξ₀ ∈ Set.Ioo lam (1 - lam),
        nclmAX r D lam δ₁ δ₂ ε σ v ξ₀ = 0
          ∧ ch * Work.Drive.sweepW' D ε ^ 2
            ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀) ∧
    (∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Icc lam (1 - lam),
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
        ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖) ∧
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

/-- The existential form of the chart data, in the shape in which the constants are produced: a
witness of `nclmDataC` together with the positivity of the constants. -/
theorem exists_nclmDataC {r : ℝ → Space} {d : BandArcData} {D : Work.Drive.SweepData d}
    {lam δ₁ δ₂ ε : ℝ} {v : Space} (h : nclmData r D lam δ₁ δ₂ ε v) :
    ∃ cℓ Cℓ ch Ch cm cE cK : ℝ,
      0 < cℓ ∧ 0 < Cℓ ∧ 0 < ch ∧ 0 < Ch ∧ 0 < cm ∧ 0 < cE ∧ 0 ≤ cK ∧
        nclmDataC r D lam δ₁ δ₂ ε v cℓ Cℓ ch Ch cm cE cK := by
  simpa only [nclmData, nclmDataC] using h

/-- The chart data with explicit constants implies the existential form. -/
theorem nclmData_of_nclmDataC {r : ℝ → Space} {d : BandArcData} {D : Work.Drive.SweepData d}
    {lam δ₁ δ₂ ε : ℝ} {v : Space} {cℓ Cℓ ch Ch cm cE cK : ℝ}
    (hcℓ : 0 < cℓ) (hCℓ : 0 < Cℓ) (hch : 0 < ch) (hCh : 0 < Ch) (hcm : 0 < cm)
    (hcE : 0 < cE) (hcK : 0 ≤ cK)
    (h : nclmDataC r D lam δ₁ δ₂ ε v cℓ Cℓ ch Ch cm cE cK) :
    nclmData r D lam δ₁ δ₂ ε v := by
  simp only [nclmData, nclmDataC]
  exact ⟨cℓ, Cℓ, ch, Ch, cm, cE, cK, hcℓ, hCℓ, hch, hCh, hcm, hcE, hcK, h⟩

end Work.Drive.Generic

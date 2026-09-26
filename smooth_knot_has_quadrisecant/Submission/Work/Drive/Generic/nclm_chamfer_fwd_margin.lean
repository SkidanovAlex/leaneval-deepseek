import Mathlib
import Submission.Work.Drive.Generic.nclmBranch

/-!
# The forward margin of a chamfer

`Work.Drive.Generic.nclmMarg` is the chart margin of `Work.Drive.Generic.needleChartLoop_margin`,
written with the loop point `Γ` and the loop velocity `V` as separate arguments.  On the arc piece
and on the chord piece of the chamfered loop the margin is bounded below by the two lemmas
`nclm_arc_margin` / `nclm_chord_margin`; on a *chamfer* the loop velocity is not one of the
elementary directions, but the velocity of a chamfer is a fixed multiple of the *deviation* `dev`
of the needle at its middle, and the margin is *linear* in `Γ`.  This module supplies the endpoint
form of the chamfer on the arc side.

The mathematics is a two-line estimate.  Writing

* `X = ⟪Γ - chartC, v⟫`, `H = ⟪Γ - chartC, chartE⟫` (the chart coordinates of the loop point),
* `a = ⟪dev, v⟫`, `b = ⟪dev, chartE⟫` (the chart coordinates of the deviation),

the hypotheses give `X ≥ ℓ/4 > 0`, `|H| ≤ 2 h0`, `b ≥ λ(1-λ)/2 · w² · cE` and
`|a| ≤ λ(1-λ)/2 · w² · cK`, together with the bookkeeping inequality `2 h0 cK ≤ ℓ cE / 8`.  The
margin is `k (X b - H a)` with `k = 2 / (λ · period)`, and

  `X b - H a ≥ (ℓ/4) b - 2 h0 |a|
             ≥ (λ(1-λ)/2 · w²) (ℓ cE/4 - 2 h0 cK)
             ≥ (λ(1-λ)/2 · w²) (ℓ cE/8) ≥ λ w² ℓ cE / 32`,

since `λ ≤ 1/2`.  Multiplying by `k` gives the announced bound.
-/

namespace Work.Drive.Generic

/-- **The scalar core of the forward chamfer margin.**  With the chart coordinates `X`, `H` of the
loop point, the chart coordinates `b`, `a` of the deviation, and the bookkeeping inequality
`2 h0 cK ≤ ℓ cE / 8`, the quantity `X b - H a` is at least `λ w² ℓ cE / 32`. -/
theorem nclm_fwd_arith {X H a b lam ℓ h0 w cE cK : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2)
    (hℓ : 0 < ℓ) (hh0 : 0 < h0) (hw : 0 < w) (hcE : 0 < cE) (hcK : 0 ≤ cK)
    (hbr : 2 * h0 * cK ≤ ℓ * cE / 8)
    (hX : ℓ / 4 ≤ X) (hH : |H| ≤ 2 * h0) (hb : lam * (1 - lam) / 2 * w ^ 2 * cE ≤ b)
    (ha : |a| ≤ lam * (1 - lam) / 2 * w ^ 2 * cK) :
    lam * w ^ 2 * ℓ * cE / 32 ≤ X * b - H * a := by
  have h1ml : 0 < 1 - lam := by linarith
  have hB0 : 0 ≤ lam * (1 - lam) / 2 * w ^ 2 * cE := by positivity
  have hb0 : 0 ≤ b := le_trans hB0 hb
  have hprod : |H * a| ≤ (2 * h0) * (lam * (1 - lam) / 2 * w ^ 2 * cK) := by
    rw [abs_mul]
    exact mul_le_mul hH ha (abs_nonneg a) (by linarith)
  have hHa_up : H * a ≤ (2 * h0) * (lam * (1 - lam) / 2 * w ^ 2 * cK) := le_of_abs_le hprod
  have hXb : ℓ / 4 * b ≤ X * b := mul_le_mul_of_nonneg_right hX hb0
  have hl4 : 0 ≤ ℓ / 4 := by linarith
  have hXb2 : ℓ / 4 * (lam * (1 - lam) / 2 * w ^ 2 * cE) ≤ ℓ / 4 * b :=
    mul_le_mul_of_nonneg_left hb hl4
  have hstep1 : ℓ / 4 * (lam * (1 - lam) / 2 * w ^ 2 * cE)
      - (2 * h0) * (lam * (1 - lam) / 2 * w ^ 2 * cK) ≤ X * b - H * a := by
    linarith [hXb, hXb2, hHa_up]
  have hfac : 0 ≤ lam * (1 - lam) * w ^ 2 / 2 := by positivity
  have hbr' : lam * (1 - lam) * w ^ 2 / 2 * (2 * h0 * cK)
      ≤ lam * (1 - lam) * w ^ 2 / 2 * (ℓ * cE / 8) :=
    mul_le_mul_of_nonneg_left hbr hfac
  have hstep2 : lam * w ^ 2 * ℓ * cE / 32
      ≤ ℓ / 4 * (lam * (1 - lam) / 2 * w ^ 2 * cE)
        - (2 * h0) * (lam * (1 - lam) / 2 * w ^ 2 * cK) := by
    have hfact : 0 ≤ lam * w ^ 2 * ℓ * cE * (1 - 2 * lam) := by
      have h0 : 0 ≤ lam := le_of_lt hlam0
      have h1 : 0 ≤ w ^ 2 * ℓ * cE := by positivity
      have h2 : 0 ≤ 1 - 2 * lam := by linarith
      nlinarith [mul_nonneg h0 (mul_nonneg h1 h2)]
    nlinarith [hbr', hfact]
  linarith [hstep1, hstep2]

/-- **The forward chamfer margin.**  With the loop point `Γ` in the forward part of the chart
(`X ≥ ℓ/4`), the ordinate bounded by `2 h0`, and the deviation `dev` aligned with `chartE`
(`⟪dev, chartE⟫ ≥ λ(1-λ)/2 w² cE`) while its `v`-component is bounded by
`λ(1-λ)/2 w² cK`, the margin of the loop travelling with velocity
`-(2/(λ·period)) • dev` is at least `w² ℓ cE / (16·period)`. -/
theorem nclm_chamfer_fwd_margin {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ ε : ℝ} {v Γ dev : LeanEval.KnotTheory.Quadrisecant.Space} {ℓ h0 w cE cK : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2)
    (hℓ : 0 < ℓ) (hh0 : 0 < h0) (hw : 0 < w) (hcE : 0 < cE) (hcK : 0 ≤ cK)
    (hbr : 2 * h0 * cK ≤ ℓ * cE / 8)
    (hX : ℓ / 4 ≤ inner ℝ (Γ - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v)
    (hHb : |inner ℝ (Γ - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
        (Work.Drive.chartE r D lam δ₁ δ₂ ε v)| ≤ 2 * h0)
    (hdevE : lam * (1 - lam) / 2 * w ^ 2 * cE
        ≤ inner ℝ dev (Work.Drive.chartE r D lam δ₁ δ₂ ε v))
    (hdevV : |inner ℝ dev v| ≤ lam * (1 - lam) / 2 * w ^ 2 * cK) :
    w ^ 2 * ℓ * cE / (16 * LeanEval.KnotTheory.Quadrisecant.period)
      ≤ Work.Drive.Generic.nclmMarg r D lam δ₁ δ₂ ε v Γ
          (-(2 / (lam * LeanEval.KnotTheory.Quadrisecant.period)) • dev) := by
  have hlow := nclm_fwd_arith hlam0 hlam2 hℓ hh0 hw hcE hcK hbr hX hHb hdevE hdevV
  have hkey : Work.Drive.Generic.nclmMarg r D lam δ₁ δ₂ ε v Γ
      (-(2 / (lam * LeanEval.KnotTheory.Quadrisecant.period)) • dev)
      = (2 / (lam * LeanEval.KnotTheory.Quadrisecant.period)) *
        (inner ℝ (Γ - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
          * inner ℝ dev (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
         - inner ℝ (Γ - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
             (Work.Drive.chartE r D lam δ₁ δ₂ ε v) * inner ℝ dev v) := by
    simp only [Work.Drive.Generic.nclmMarg, real_inner_smul_left]
    ring
  rw [hkey]
  have hA : w ^ 2 * ℓ * cE / (16 * LeanEval.KnotTheory.Quadrisecant.period)
      = (2 / (lam * LeanEval.KnotTheory.Quadrisecant.period))
        * (lam * w ^ 2 * ℓ * cE / 32) := by
    have hper : (0:ℝ) < LeanEval.KnotTheory.Quadrisecant.period :=
      LeanEval.KnotTheory.Quadrisecant.period_pos
    have hpne : LeanEval.KnotTheory.Quadrisecant.period ≠ 0 := ne_of_gt hper
    have hlne : lam ≠ 0 := ne_of_gt hlam0
    field_simp
    ring
  rw [hA]
  have hper : (0:ℝ) < LeanEval.KnotTheory.Quadrisecant.period :=
    LeanEval.KnotTheory.Quadrisecant.period_pos
  have hpos : (0:ℝ) < 2 / (lam * LeanEval.KnotTheory.Quadrisecant.period) :=
    div_pos (by norm_num) (mul_pos hlam0 hper)
  exact mul_le_mul_of_nonneg_left hlow hpos.le

end Work.Drive.Generic

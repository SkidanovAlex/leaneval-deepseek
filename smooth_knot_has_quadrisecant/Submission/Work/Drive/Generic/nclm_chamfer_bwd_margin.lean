import Mathlib
import Submission.Work.Drive.Generic.nclmBranch

/-!
# The backward (tail) chamfer margin of the needle's chart

`Work.Drive.Generic.nclmMarg r D lam δ₁ δ₂ ε v Γ V` is the bilinear chart margin
`⟪Γ - chartC, chartE⟫ * ⟪V, v⟫ - ⟪Γ - chartC, v⟫ * ⟪V, chartE⟫` of the needle's chart.  This
module proves the *backward* endpoint form of the chamfer bound: if the chamfer point `Γ` lies at
abscissa `≤ -ℓ/4` (i.e. behind the chart centre along `v`), its ordinate is bounded by `2 * h0`,
and the chamfer direction `(2 / (lam * period)) • dev` has an `E`-component of at least
`lam (1-lam) / 2 * w² * cE` and a `v`-component bounded by `lam (1-lam) / 2 * w² * cK`, then the
margin is at least `w² ℓ cE / (16 period)`.

The content is the elementary estimate
`margin ≥ (2/(lam period)) * m * (ℓ cE/4 - 2 h0 cK)` with `m = lam (1-lam)/2 * w²`, which equals
`((1 - lam) w² / period) * (ℓ cE/4 - 2 h0 cK)`, and the hypothesis `2 h0 cK ≤ ℓ cE / 8` together
with `lam < 1/2` then gives the stated bound.  No smoothness of `r`, `d` or `D` is used: the
statement is a pure estimate in the inner-product data.
-/

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant

theorem nclm_chamfer_bwd_margin {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ ε : ℝ} {v Γ dev : LeanEval.KnotTheory.Quadrisecant.Space} {ℓ h0 w cE cK : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2)
    (hℓ : 0 < ℓ) (hh0 : 0 < h0) (hw : 0 < w) (hcE : 0 < cE) (hcK : 0 ≤ cK)
    (hbr : 2 * h0 * cK ≤ ℓ * cE / 8)
    (hX : inner ℝ (Γ - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v ≤ -ℓ / 4)
    (hHb : |inner ℝ (Γ - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
        (Work.Drive.chartE r D lam δ₁ δ₂ ε v)| ≤ 2 * h0)
    (hdevE : lam * (1 - lam) / 2 * w ^ 2 * cE
        ≤ inner ℝ dev (Work.Drive.chartE r D lam δ₁ δ₂ ε v))
    (hdevV : |inner ℝ dev v| ≤ lam * (1 - lam) / 2 * w ^ 2 * cK) :
    w ^ 2 * ℓ * cE / (16 * LeanEval.KnotTheory.Quadrisecant.period)
      ≤ Work.Drive.Generic.nclmMarg r D lam δ₁ δ₂ ε v Γ
          ((2 / (lam * LeanEval.KnotTheory.Quadrisecant.period)) • dev) := by
  have hp : (0 : ℝ) < period := period_pos
  -- `hcK` is not used by the estimate itself (the hypothesis is vacuous when `cK < 0`);
  -- it is recorded here so that the statement's binder is referenced.
  have _ : (0 : ℝ) ≤ cK := hcK
  set C : Space := Work.Drive.chartC r D lam δ₁ δ₂ ε v with hC
  set E : Space := Work.Drive.chartE r D lam δ₁ δ₂ ε v with hE
  have hkpos : (0 : ℝ) < 2 / (lam * period) := div_pos two_pos (mul_pos hlam0 hp)
  -- unfold the margin as `k` times the `(v, E)`-bracket
  have hmarg : nclmMarg r D lam δ₁ δ₂ ε v Γ ((2 / (lam * period)) • dev)
      = (2 / (lam * period)) * (inner ℝ (Γ - C) E * inner ℝ dev v
          - inner ℝ (Γ - C) v * inner ℝ dev E) := by
    simp only [nclmMarg]
    rw [← hC, ← hE, real_inner_smul_left, real_inner_smul_left]
    ring
  rw [hmarg]
  -- the two symmetric pointwise estimates
  have hprod1 : -(2 * h0 * (lam * (1 - lam) / 2 * w ^ 2 * cK))
      ≤ inner ℝ (Γ - C) E * inner ℝ dev v := by
    have habs : |inner ℝ (Γ - C) E * inner ℝ dev v|
        ≤ 2 * h0 * (lam * (1 - lam) / 2 * w ^ 2 * cK) := by
      rw [abs_mul]
      exact mul_le_mul hHb hdevV (abs_nonneg _) (by linarith [hh0])
    exact neg_le_of_abs_le habs
  have hprod2 : (ℓ / 4) * (lam * (1 - lam) / 2 * w ^ 2 * cE)
      ≤ (-inner ℝ (Γ - C) v) * inner ℝ dev E := by
    have h1 : ℓ / 4 ≤ -inner ℝ (Γ - C) v := by linarith
    have h4 : 0 ≤ -inner ℝ (Γ - C) v := by linarith
    have h3 : (0 : ℝ) ≤ lam * (1 - lam) / 2 * w ^ 2 * cE := by
      have h1' : 0 ≤ 1 - lam := by linarith
      positivity
    exact mul_le_mul h1 hdevE h3 h4
  -- the bracket lower bound
  have hbrk : (ℓ / 4) * (lam * (1 - lam) / 2 * w ^ 2 * cE)
        - 2 * h0 * (lam * (1 - lam) / 2 * w ^ 2 * cK)
      ≤ inner ℝ (Γ - C) E * inner ℝ dev v - inner ℝ (Γ - C) v * inner ℝ dev E := by
    have h2 : (ℓ / 4) * (lam * (1 - lam) / 2 * w ^ 2 * cE)
        ≤ -(inner ℝ (Γ - C) v * inner ℝ dev E) := by
      have heq : (-inner ℝ (Γ - C) v) * inner ℝ dev E
          = -(inner ℝ (Γ - C) v * inner ℝ dev E) := by ring
      rw [← heq]; exact hprod2
    linarith [hprod1, h2]
  have hscaled := mul_le_mul_of_nonneg_left hbrk hkpos.le
  -- the algebraic simplification of the scaled bracket
  have hstep_i : (2 / (lam * period)) * ((ℓ / 4) * (lam * (1 - lam) / 2 * w ^ 2 * cE)
        - 2 * h0 * (lam * (1 - lam) / 2 * w ^ 2 * cK))
      = (1 - lam) * w ^ 2 / period * (ℓ * cE / 4 - 2 * h0 * cK) := by
    have hln : lam ≠ 0 := ne_of_gt hlam0
    have hpn : period ≠ 0 := ne_of_gt hp
    field_simp
  -- the pure arithmetic estimate
  have hstep_ii : w ^ 2 * ℓ * cE / (16 * period)
      ≤ (1 - lam) * w ^ 2 / period * (ℓ * cE / 4 - 2 * h0 * cK) := by
    have hLE : 0 < ℓ * cE := mul_pos hℓ hcE
    have hnl : 0 ≤ 1 - lam := by linarith
    have hkey : ℓ * cE / 16 ≤ (1 - lam) * (ℓ * cE / 4 - 2 * h0 * cK) := by
      have h1 : ℓ * cE / 8 ≤ ℓ * cE / 4 - 2 * h0 * cK := by linarith [hbr]
      have h2 : (1 - lam) * (ℓ * cE / 8) ≤ (1 - lam) * (ℓ * cE / 4 - 2 * h0 * cK) :=
        mul_le_mul_of_nonneg_left h1 hnl
      have h3 : ℓ * cE / 16 ≤ (1 - lam) * (ℓ * cE / 8) := by
        have hnn : 0 ≤ (1 - 2 * lam) * (ℓ * cE) := mul_nonneg (by linarith) hLE.le
        nlinarith [hnn]
      linarith
    have hwp : 0 < w ^ 2 / period := by positivity
    have hsc := mul_le_mul_of_nonneg_left hkey hwp.le
    calc w ^ 2 * ℓ * cE / (16 * period)
        = w ^ 2 / period * (ℓ * cE / 16) := by ring
      _ ≤ w ^ 2 / period * ((1 - lam) * (ℓ * cE / 4 - 2 * h0 * cK)) := hsc
      _ = (1 - lam) * w ^ 2 / period * (ℓ * cE / 4 - 2 * h0 * cK) := by ring
  calc w ^ 2 * ℓ * cE / (16 * period)
      ≤ (1 - lam) * w ^ 2 / period * (ℓ * cE / 4 - 2 * h0 * cK) := hstep_ii
    _ = (2 / (lam * period)) * ((ℓ / 4) * (lam * (1 - lam) / 2 * w ^ 2 * cE)
          - 2 * h0 * (lam * (1 - lam) / 2 * w ^ 2 * cK)) := hstep_i.symm
    _ ≤ (2 / (lam * period)) * (inner ℝ (Γ - C) E * inner ℝ dev v
          - inner ℝ (Γ - C) v * inner ℝ dev E) := hscaled

end Work.Drive.Generic

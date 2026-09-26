import Mathlib
import Submission.Work.Drive.Generic.nclmBranch

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant

/-!
# The chord piece of the chart margin

The chart margin `Work.Drive.Generic.nclmMarg r D lam δ₁ δ₂ ε v Γ V` is the bilinear expression

  `⟪Γ - chartC, chartE⟫ * ⟪V, v⟫ - ⟪Γ - chartC, v⟫ * ⟪V, chartE⟫`.

On the **chord branch** of the loop the point is `Γ = sweepChord' r D σ ξ`, a convex combination of
the two ends `r (taR D σ)`, `r (tbR D σ)` of the retained arc, while the loop velocity is a negative
multiple of the chord `r (tbR D σ) - r (taR D σ)`.

The geometric content of the requested estimate is *entirely* the four signs supplied as hypotheses:
the two ends of the retained arc sit *below* the chart centre in the `chartE` coordinate
(`hHA`, `hHB`), so the whole chord does too (`hPe`); the chord's `v`-coordinates are bounded by
`ℓ/2` (`hXAb`, `hXBb`), so every point of the chord is (`hPv`); the chord has `v`-length at least
`ℓ/2` (`hxW`), so the (negative) velocity has a definite negative `v`-component (`hVv`); and the
velocity is *almost* annihilated by `chartE` (`hhW`, `hVe`).

Combining: the first product of `nclmMarg` is `≥ c ℓ h0 / 4` and the second is `≤ c ℓ h0 / 16` in
absolute value, with `c = (1 - 2 lam) / ((1/2 - lam) * period) = 2 / period`.  Hence

  `nclmMarg ≥ 3 c ℓ h0 / 16 = 3 ℓ h0 / (8 * period) ≥ 3 ℓ h0 / (16 * period)`,
-/

/-- **The arithmetic core of the chord margin.**  The product of two negative chart coordinates
dominates the product of the two small ones. -/
theorem nclm_chord_arith {P Q R S c ℓ h0 : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) (hh0 : 0 < h0)
    (hP : P ≤ -h0 / 2) (hQ : Q ≤ -(c * (ℓ / 2))) (hR : |R| ≤ ℓ / 2)
    (hS : |S| ≤ c * (h0 / 8)) :
    c * ℓ * h0 / 4 - c * ℓ * h0 / 16 ≤ P * Q - R * S := by
  have hPQ : c * ℓ * h0 / 4 ≤ P * Q := by
    have h1 : h0 / 2 ≤ -P := by linarith
    have h2 : c * (ℓ / 2) ≤ -Q := by linarith
    have h3 : (0 : ℝ) ≤ c * (ℓ / 2) := by positivity
    have h4 : (0 : ℝ) ≤ -P := by linarith
    have hkey := mul_le_mul h1 h2 h3 h4
    have heq : (-P) * (-Q) = P * Q := by ring
    linarith [hkey]
  have hRS : R * S ≤ c * ℓ * h0 / 16 := by
    have h1 : |R * S| ≤ ℓ / 2 * (c * (h0 / 8)) := by
      rw [abs_mul]
      exact mul_le_mul hR hS (abs_nonneg _) (by positivity)
    have h2 : ℓ / 2 * (c * (h0 / 8)) = c * ℓ * h0 / 16 := by ring
    rw [h2] at h1
    exact (abs_le.mp h1).2
  linarith [hPQ, hRS]

theorem nclm_chord_margin {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ ε σ ξ ℓ h0 : ℝ} {v : LeanEval.KnotTheory.Quadrisecant.Space}
    (hlam0 : 0 < lam) (hlam4 : lam ≤ 1 / 4) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hℓ : 0 < ℓ) (hh0 : 0 < h0)
    (hXAb : |inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v| ≤ ℓ / 2)
    (hXBb : |inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v| ≤ ℓ / 2)
    (hHA : inner ℝ (r (Work.Drive.taR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
        (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ≤ -h0 / 2)
    (hHB : inner ℝ (r (Work.Drive.tbR D σ) - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
        (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ≤ -h0 / 2)
    (hxW : ℓ / 2 ≤ inner ℝ (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ)) v)
    (hhW : |inner ℝ (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))
        (Work.Drive.chartE r D lam δ₁ δ₂ ε v)| ≤ h0 / 8) :
    3 * ℓ * h0 / (16 * LeanEval.KnotTheory.Quadrisecant.period)
      ≤ Work.Drive.Generic.nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepChord' r D σ ξ)
          (-((1 - 2 * lam) / ((1 / 2 - lam) * LeanEval.KnotTheory.Quadrisecant.period)) •
            (r (Work.Drive.tbR D σ) - r (Work.Drive.taR D σ))) := by
  have hper : (0 : ℝ) < period := period_pos
  rw [Work.Drive.Generic.nclmMarg]
  set e : Space := Work.Drive.chartE r D lam δ₁ δ₂ ε v with he
  set C : Space := Work.Drive.chartC r D lam δ₁ δ₂ ε v with hC
  set A : Space := r (Work.Drive.taR D σ) with hA
  set B : Space := r (Work.Drive.tbR D σ) with hB
  -- the (positive) factor multiplying the chord
  have hq : 0 < (1 - 2 * lam) / ((1 / 2 - lam) * period) := by
    have h1 : 0 < 1 - 2 * lam := by linarith
    have h2 : 0 < (1 / 2 - lam) * period := by
      have h3 : 0 < 1 / 2 - lam := by linarith
      positivity
    exact div_pos h1 h2
  -- the point of the chord is a convex combination of its two ends
  have hchord : Work.Drive.sweepChord' r D σ ξ - C = (1 - ξ) • (A - C) + ξ • (B - C) := by
    show (1 - ξ) • r (Work.Drive.taR D σ) + ξ • r (Work.Drive.tbR D σ) - C
      = (1 - ξ) • (A - C) + ξ • (B - C)
    rw [← hA, ← hB, smul_sub, smul_sub]
    module
  -- the `chartE`-coordinate of the chord
  have hPe : inner ℝ (Work.Drive.sweepChord' r D σ ξ - C) e ≤ -h0 / 2 := by
    rw [hchord, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left hHA (by linarith : (0 : ℝ) ≤ 1 - ξ),
      mul_le_mul_of_nonneg_left hHB hξ0]
  -- the `v`-coordinate of the chord
  have hPv : |inner ℝ (Work.Drive.sweepChord' r D σ ξ - C) v| ≤ ℓ / 2 := by
    rw [hchord, inner_add_left, real_inner_smul_left, real_inner_smul_left, abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp hXAb).1 (by linarith : (0 : ℝ) ≤ 1 - ξ),
        mul_le_mul_of_nonneg_left (abs_le.mp hXBb).1 hξ0]
    · nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp hXAb).2 (by linarith : (0 : ℝ) ≤ 1 - ξ),
        mul_le_mul_of_nonneg_left (abs_le.mp hXBb).2 hξ0]
  -- the `v`-component of the (negative) velocity
  have hVv : inner ℝ (-((1 - 2 * lam) / ((1 / 2 - lam) * period)) • (B - A)) v
      ≤ -(((1 - 2 * lam) / ((1 / 2 - lam) * period)) * (ℓ / 2)) := by
    rw [neg_smul, inner_neg_left, real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left hxW hq.le]
  -- the `chartE`-component of the velocity is small
  have hVe : |inner ℝ (-((1 - 2 * lam) / ((1 / 2 - lam) * period)) • (B - A)) e|
      ≤ ((1 - 2 * lam) / ((1 / 2 - lam) * period)) * (h0 / 8) := by
    rw [neg_smul, inner_neg_left, real_inner_smul_left, abs_neg, abs_mul, abs_of_pos hq]
    exact mul_le_mul_of_nonneg_left hhW hq.le
  have hcore := nclm_chord_arith hq hℓ hh0 hPe hVv hPv hVe
  -- the factor equals `2 / period`
  have hq2 : (1 - 2 * lam) / ((1 / 2 - lam) * period) = 2 / period := by
    have hdne : (1 / 2 - lam) * period ≠ 0 := by
      have h3 : 0 < 1 / 2 - lam := by linarith
      positivity
    have hpne : period ≠ 0 := ne_of_gt hper
    have hne : (1 : ℝ) - 2 * lam ≠ 0 := by linarith
    field_simp
    try ring
  -- and then the bound is the sharp `3 ℓ h0 / (8 * period)`
  have hstep : 3 * ℓ * h0 / (16 * period)
      ≤ (1 - 2 * lam) / ((1 / 2 - lam) * period) * ℓ * h0 / 4
        - (1 - 2 * lam) / ((1 / 2 - lam) * period) * ℓ * h0 / 16 := by
    rw [hq2]
    have hkey : (0 : ℝ) < ℓ * h0 / period := by positivity
    have e1 : 2 / period * ℓ * h0 / 4 - 2 / period * ℓ * h0 / 16
        = 3 / 8 * (ℓ * h0 / period) := by
      field_simp
      try ring
    have e2 : 3 * ℓ * h0 / (16 * period) = 3 / 16 * (ℓ * h0 / period) := by
      field_simp
      try ring
    rw [e1, e2]
    nlinarith [hkey]
  linarith [hcore, hstep]

end Work.Drive.Generic

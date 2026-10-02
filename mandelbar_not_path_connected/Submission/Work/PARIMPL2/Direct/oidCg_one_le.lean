import Mathlib
import Submission.Work.PARIMPL2.Direct.oidDefs
import Submission.Work.PARIMPL2.Direct.one_term_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Pointwise bound for the growth coefficient.  On the window
`R/4 + 2 ≤ x_j ≤ π/λ - R/4` with `λ > 0`, `R ≥ 128`, `λ R² ≤ 1`, the one-term estimate
`one_term_le` combines with `x_j ≥ R/4 + 2`, `π/λ - x_j ≥ R/4` and `λ ≤ 1/R²` to give
`oidCg λ 1 x y j ≤ 33/R²`. -/
theorem oidCg_one_le (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (x y : ℕ → ℝ) (j : ℕ)
    (hx1 : R / 4 + 2 ≤ x j) (hx2 : x j ≤ Real.pi / lam - R / 4)
    (hDpos : 0 < Work.PARIMPL2.Direct.ocDen lam x y j) :
    Work.PARIMPL2.Direct.oidCg lam 1 x y j ≤ 33 / R ^ 2 := by
  have hD' : 0 < Real.sin (lam * x j) ^ 2 + Real.sinh (lam * y j) ^ 2 := by
    simpa [ocDen] using hDpos
  have hRpos : (0 : ℝ) < R := by linarith
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hx0 : 0 < x j := by linarith
  have hX2pos : (0 : ℝ) < (x j) ^ 2 := pow_pos hx0 2
  have hYpos : 0 < Real.pi / lam - x j := by
    have : 0 < R / 4 := by linarith
    linarith [hx2]
  have hY2pos : (0 : ℝ) < (Real.pi / lam - x j) ^ 2 := pow_pos hYpos 2
  -- Cleared form of the two "distance" bounds.
  have hRX : R ^ 2 ≤ 16 * (x j) ^ 2 := by nlinarith [hx1, hR, hx0]
  have hRY : R ^ 2 ≤ 16 * (Real.pi / lam - x j) ^ 2 := by
    have hge : R / 4 ≤ Real.pi / lam - x j := by linarith [hx2]
    nlinarith [hge, hYpos, hR]
  -- `2 λ² R² ≤ 1`.
  have hZ : 2 * lam ^ 2 * R ^ 2 ≤ 1 := by
    have hp : lam ^ 2 * R ^ 2 ≤ lam := by
      have h := mul_le_mul_of_nonneg_left hlamR hlam.le
      nlinarith [h]
    have h2lam : 2 * lam ≤ 1 := by
      have hR2ge2 : (0 : ℝ) ≤ R ^ 2 - 2 := by nlinarith [hR]
      have hprod : 0 ≤ lam * (R ^ 2 - 2) := mul_nonneg hlam.le hR2ge2
      nlinarith [hprod, hlamR]
    linarith
  -- The two distance terms, multiplied by `R²`, are at most `16`.
  have hA : (1 / (x j) ^ 2) * R ^ 2 ≤ 16 := by
    have he : (1 / (x j) ^ 2) * R ^ 2 = R ^ 2 / (x j) ^ 2 := by ring
    rw [he, div_le_iff₀ hX2pos]
    exact hRX
  have hB : (1 / (Real.pi / lam - x j) ^ 2) * R ^ 2 ≤ 16 := by
    have he : (1 / (Real.pi / lam - x j) ^ 2) * R ^ 2 = R ^ 2 / (Real.pi / lam - x j) ^ 2 := by
      ring
    rw [he, div_le_iff₀ hY2pos]
    exact hRY
  have hkey := one_term_le lam R (x j) (y j) hlam hR hx1 hx2
  -- Clear the denominator `R²` once and for all.
  have hfinal :
      (lam ^ 2 + lam ^ 2 / (Real.sin (lam * x j) ^ 2 + Real.sinh (lam * y j) ^ 2)) * R ^ 2
        ≤ 33 := by
    have hstep :
        (lam ^ 2 + lam ^ 2 / (Real.sin (lam * x j) ^ 2 + Real.sinh (lam * y j) ^ 2)) * R ^ 2
          ≤ (2 * lam ^ 2 + 1 / (x j) ^ 2 + 1 / (Real.pi / lam - x j) ^ 2) * R ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hR2pos.le
      linarith [hkey]
    have heq : (2 * lam ^ 2 + 1 / (x j) ^ 2 + 1 / (Real.pi / lam - x j) ^ 2) * R ^ 2
        = 2 * lam ^ 2 * R ^ 2 + (1 / (x j) ^ 2) * R ^ 2
          + (1 / (Real.pi / lam - x j) ^ 2) * R ^ 2 := by ring
    rw [heq] at hstep
    linarith [hstep, hA, hB, hZ]
  rw [oidCg, ocDen, one_mul, le_div_iff₀ hR2pos]
  exact hfinal

end Work.PARIMPL2.Direct

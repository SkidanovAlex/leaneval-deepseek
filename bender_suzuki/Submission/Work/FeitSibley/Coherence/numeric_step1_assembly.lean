import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.FeitSibley.Coherence

/-- **Numeric contradiction (App. XII, step (1)).**

Assume `D ≥ 1`, `SSc ≥ 1`, `Q2c, Zc, QI, c > 0`/`≥ 0` with `Q2c < QI` and

* `D · SSc · (QI/Q2c - 1) ≤ 2 D c`,
* `c² · Zc ≤ D² · QI`,
* `Zc/Q2c ≥ D + 1` and `QI/Zc ≥ D + 1`.

Then this is impossible.

Indeed, from the first two, `QI/Q2c ≤ 1 + 2c` and `(D+1)² ≤ QI/Q2c`, so `2c ≥ D² + 2D`.
From the third and fourth, `(D+1) c² / D² ≤ QI/Q2c ≤ 1 + 2c`, hence `(D+1) c² ≤ D²(1+2c)`.
Writing `P(x) = (D+1)x² - 2D²x - D²`, the second batch says `P(c) ≤ 0`, while
`P(c) = D⁴(D+1)/4 + (D+1)/4·(2c - D² - 2D)² + D(D²+D+2)/2·(2c - D² - 2D)`,
a sum of nonnegative terms in which the first is `> 0` for `D ≥ 1`.  Contradiction. -/
theorem numeric_step1_assembly {D SSc QI Q2c Zc c : ℝ} (hD : 1 ≤ D) (hSSc : 1 ≤ SSc)
    (hQ2c : 0 < Q2c) (hZc : 0 < Zc) (hQ1 : 0 < QI) (hc : 0 ≤ c) (hQ2lt : Q2c < QI)
    (hA : D * SSc * (QI / Q2c - 1) ≤ 2 * D * c) (hB : c ^ 2 * Zc ≤ D ^ 2 * QI)
    (hz1 : D + 1 ≤ Zc / Q2c) (hx2 : D + 1 ≤ QI / Zc) : False := by
  have hDpos : 0 < D := by linarith
  -- `QI/Q2c - 1 > 0`, since `QI > Q2c`.
  have hr : 0 < QI / Q2c - 1 := by
    have : 1 < QI / Q2c := by rw [lt_div_iff₀ hQ2c]; linarith
    linarith
  -- Drop the factor `SSc ≥ 1` from `hA`.
  have hA' : D * (QI / Q2c - 1) ≤ 2 * D * c := by
    have hprod : 0 ≤ D * (SSc - 1) * (QI / Q2c - 1) :=
      mul_nonneg (mul_nonneg hDpos.le (by linarith)) hr.le
    nlinarith [hA, hprod]
  -- Hence `QI/Q2c ≤ 1 + 2c`.
  have h_le1 : QI / Q2c ≤ 1 + 2 * c := by
    have h2 : D * (QI / Q2c - 1) ≤ D * (2 * c) := by nlinarith [hA']
    have h3 := le_of_mul_le_mul_left h2 hDpos
    linarith
  -- `QI/Q2c = (QI/Zc) * (Zc/Q2c)`.
  have heq : QI / Q2c = (QI / Zc) * (Zc / Q2c) := by field_simp
  have hD1 : (0 : ℝ) ≤ D + 1 := by linarith
  have hb : (0 : ℝ) ≤ QI / Zc := by positivity
  -- `(D+1)² ≤ QI/Q2c`.
  have hprod_low : (D + 1) * (D + 1) ≤ (QI / Zc) * (Zc / Q2c) := mul_le_mul hx2 hz1 hD1 hb
  have h_low : (D + 1) ^ 2 ≤ QI / Q2c := by rw [heq]; nlinarith [hprod_low]
  -- Consequently `2c ≥ D² + 2D`.
  have h_c_low : D ^ 2 + 2 * D ≤ 2 * c := by nlinarith [h_low, h_le1]
  -- From `hB`: `c² ≤ D² · (QI/Zc)`.
  have hB' : c ^ 2 ≤ D ^ 2 * (QI / Zc) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hZc).mpr hB
  have hv : c ^ 2 / D ^ 2 ≤ QI / Zc := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < D ^ 2)]
    nlinarith [hB']
  have hb2 : (0 : ℝ) ≤ QI / Zc := by positivity
  -- `(c²/D²) * (D+1) ≤ QI/Q2c`.
  have hstep : (c ^ 2 / D ^ 2) * (D + 1) ≤ QI / Q2c := by
    rw [heq]
    calc (c ^ 2 / D ^ 2) * (D + 1) ≤ (QI / Zc) * (D + 1) :=
          mul_le_mul_of_nonneg_right hv hD1
      _ ≤ (QI / Zc) * (Zc / Q2c) := mul_le_mul_of_nonneg_left hz1 hb2
  -- Hence `(D+1) c² ≤ D² (1 + 2c)`.
  have h_c_high : (D + 1) * c ^ 2 ≤ D ^ 2 * (1 + 2 * c) := by
    have h3 : (c ^ 2 / D ^ 2) * (D + 1) ≤ 1 + 2 * c := by linarith [hstep, h_le1]
    have h4 : ((c ^ 2 / D ^ 2) * (D + 1)) * D ^ 2 ≤ (1 + 2 * c) * D ^ 2 :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have h5 : (c ^ 2 / D ^ 2) * (D + 1) * D ^ 2 = (D + 1) * c ^ 2 := by field_simp
    rw [h5] at h4
    linarith [h4]
  -- The quadratic `P(c) = (D+1) c² - 2 D² c - D²` is strictly positive.
  have key : (0 : ℝ) < (D + 1) * c ^ 2 - 2 * D ^ 2 * c - D ^ 2 := by
    have hu : 0 ≤ 2 * c - D ^ 2 - 2 * D := by linarith
    have h3 : 0 ≤ (D + 1) / 4 * (2 * c - D ^ 2 - 2 * D) ^ 2 := by positivity
    have h4 : 0 ≤ D * (D ^ 2 + D + 2) / 2 * (2 * c - D ^ 2 - 2 * D) := by
      have hnn : (0 : ℝ) ≤ D * (D ^ 2 + D + 2) / 2 := by nlinarith [sq_nonneg D]
      exact mul_nonneg hnn hu
    have h5 : 0 < D ^ 4 * (D + 1) / 4 := by positivity
    nlinarith [h3, h4, h5]
  -- But `h_c_high` says `P(c) ≤ 0`.
  nlinarith [h_c_high, key]

end Work.FeitSibley.Coherence

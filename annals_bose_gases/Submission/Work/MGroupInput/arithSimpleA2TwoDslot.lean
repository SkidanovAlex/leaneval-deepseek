import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

/-- Arithmetic core of the two-dimensional (`D`-slot) part of the per-state
assembly: with `ε := 1/20` and `x ≥ 20`, the "Bogoliubov slot"

`(1/2) D (x+1)²/V − (1/2) ((1+ε) D + ε av) ((x+1) x / V)`

dominates `(4π (x+1)(1−εx) − ε/2 · x(x+1)) · av / V` whenever `0 ≤ D ≤ 8π av`.

Indeed, after multiplying by the positive `V`, the difference of the two sides
is `(x+1) · (1/2) · (1 − x/20) · (D − 8π av) ≥ 0`, a product of two nonpositive
factors. -/
lemma arithSimpleA2TwoDslot {x av D V : ℝ} (hav : 0 < av) (hV : 0 < V)
    (hD0 : 0 ≤ D) (hD1 : D ≤ 8 * Real.pi * av) (hx : 20 ≤ x) :
    (1 / 2) * D * (x + 1) ^ 2 * V⁻¹
      - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av) * ((x + 1) * x * V⁻¹)
      ≥ (4 * Real.pi * (x + 1) * (1 - x / 20) - (1 / 40) * x * (x + 1)) * (av * V⁻¹) := by
  have hx1 : (0 : ℝ) ≤ x + 1 := by linarith
  have h1x : 1 - x / 20 ≤ 0 := by linarith
  have hD8 : D - 8 * Real.pi * av ≤ 0 := by linarith
  have hprod : 0 ≤ (1 - x / 20) * (D - 8 * Real.pi * av) :=
    mul_nonneg_of_nonpos_of_nonpos h1x hD8
  have hcore : 0 ≤ (1 / 2) * D * (x + 1) ^ 2
      - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av) * ((x + 1) * x)
      - (4 * Real.pi * (x + 1) * (1 - x / 20) - (1 / 40) * x * (x + 1)) * av := by
    have e : (1 / 2) * D * (x + 1) ^ 2
        - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av) * ((x + 1) * x)
        - (4 * Real.pi * (x + 1) * (1 - x / 20) - (1 / 40) * x * (x + 1)) * av
        = (x + 1) * ((1 / 2) * ((1 - x / 20) * (D - 8 * Real.pi * av))) := by ring
    rw [e]
    exact mul_nonneg hx1 (mul_nonneg (by norm_num) hprod)
  have hVinv : 0 ≤ V⁻¹ := le_of_lt (inv_pos.mpr hV)
  have hfin : 0 ≤ ((1 / 2) * D * (x + 1) ^ 2
      - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av) * ((x + 1) * x)
      - (4 * Real.pi * (x + 1) * (1 - x / 20) - (1 / 40) * x * (x + 1)) * av) * V⁻¹ :=
    mul_nonneg hcore hVinv
  have e2 : (1 / 2) * D * (x + 1) ^ 2 * V⁻¹
      - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av) * ((x + 1) * x * V⁻¹)
      - (4 * Real.pi * (x + 1) * (1 - x / 20) - (1 / 40) * x * (x + 1)) * (av * V⁻¹)
      = ((1 / 2) * D * (x + 1) ^ 2
      - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av) * ((x + 1) * x)
      - (4 * Real.pi * (x + 1) * (1 - x / 20) - (1 / 40) * x * (x + 1)) * av) * V⁻¹ := by ring
  have hdiff : 0 ≤ (1 / 2) * D * (x + 1) ^ 2 * V⁻¹
      - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av) * ((x + 1) * x * V⁻¹)
      - (4 * Real.pi * (x + 1) * (1 - x / 20) - (1 / 40) * x * (x + 1)) * (av * V⁻¹) := by
    rw [e2]
    exact hfin
  linarith

end Work.MGroupInput

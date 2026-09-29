import Mathlib

namespace Work.TMC7Core.Scale

theorem rtlSumFinalArith (cκ C₀ : ℝ) (Q₀ : ℕ) (Sb : ℕ) (hcκ : 0 < cκ) (hC₀ : 0 ≤ C₀) :
    (Sb : ℝ) * ((76 * C₀ + 9) * Real.exp (-(cκ * (Q₀ : ℝ) / 2))
        * (1 - Real.exp (-(cκ / 2)))⁻¹)
      ≤ (Sb + 1) * (76 * C₀ + 9) * Real.exp (-(cκ * (Q₀ : ℝ) / 2))
          / (1 - Real.exp (-(cκ / 2))) := by
  -- The common positive factor: `1 - exp(-(cκ/2)) > 0` since `cκ > 0`.
  have h1 : (0 : ℝ) < 1 - Real.exp (-(cκ / 2)) := by
    have h : Real.exp (-(cκ / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  -- The nonnegative common factor multiplying `Sb` resp. `Sb + 1`.
  have hK : 0 ≤ (76 * C₀ + 9) * Real.exp (-(cκ * (Q₀ : ℝ) / 2))
      * (1 - Real.exp (-(cκ / 2)))⁻¹ := by
    have hA : 0 ≤ 76 * C₀ + 9 := by linarith
    have he : 0 < Real.exp (-(cκ * (Q₀ : ℝ) / 2)) := Real.exp_pos _
    have hi : 0 ≤ (1 - Real.exp (-(cκ / 2)))⁻¹ := inv_nonneg.mpr (le_of_lt h1)
    exact mul_nonneg (mul_nonneg hA he.le) hi
  have hSb : (Sb : ℝ) ≤ ((Sb + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ Sb
  calc (Sb : ℝ) * ((76 * C₀ + 9) * Real.exp (-(cκ * (Q₀ : ℝ) / 2))
          * (1 - Real.exp (-(cκ / 2)))⁻¹)
      ≤ ((Sb + 1 : ℕ) : ℝ) * ((76 * C₀ + 9) * Real.exp (-(cκ * (Q₀ : ℝ) / 2))
          * (1 - Real.exp (-(cκ / 2)))⁻¹) :=
        mul_le_mul_of_nonneg_right hSb hK
    _ = (Sb + 1) * (76 * C₀ + 9) * Real.exp (-(cκ * (Q₀ : ℝ) / 2))
          / (1 - Real.exp (-(cκ / 2))) := by
        rw [div_eq_mul_inv]; push_cast; ring

end Work.TMC7Core.Scale

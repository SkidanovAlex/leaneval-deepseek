import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

/-- For `0 < s ≤ 1` and `0 < α` one has `s ^ (1 - α / 5) / (α + s) ≤ 2`.

In fact the sharper bound `s ^ (1 - α / 5) / (α + s) ≤ 1` holds: Bernoulli's
inequality for the exponent `α / 5 ∈ (0, 1)` applied with `s' = 1 / s - 1 ≥ 0` gives
`(1 / s) ^ (α / 5) ≤ 1 + (α / 5) (1 / s - 1)`, and multiplying by `s > 0` yields
`s ^ (1 - α / 5) ≤ s + (α / 5) (1 - s) ≤ α + s`. -/
theorem sin_two_rpow_div_le (α s : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hs : 0 < s)
    (hs1 : s ≤ 1) : s ^ (1 - α / 5) / (α + s) ≤ 2 := by
  have hp1 : (0 : ℝ) ≤ α / 5 := by linarith
  have hp2 : α / 5 ≤ 1 := by linarith
  have h1 : (-1 : ℝ) ≤ s⁻¹ - 1 := by
    have : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
    linarith
  have hb := rpow_one_add_le_one_add_mul_self h1 hp1 hp2
  simp only [add_sub_cancel] at hb
  have hb' : s * s⁻¹ ^ (α / 5) ≤ s * (1 + (α / 5) * (s⁻¹ - 1)) :=
    mul_le_mul_of_nonneg_left hb hs.le
  have hpow : s * s⁻¹ ^ (α / 5) = s ^ (1 - α / 5) := by
    calc s * s⁻¹ ^ (α / 5) = s * (s ^ (α / 5))⁻¹ := by rw [Real.inv_rpow hs.le]
      _ = s / s ^ (α / 5) := rfl
      _ = s ^ (1 : ℝ) / s ^ (α / 5) := by rw [Real.rpow_one]
      _ = s ^ (1 - α / 5) := (Real.rpow_sub hs 1 (α / 5)).symm
  have hrhs : s * (1 + (α / 5) * (s⁻¹ - 1)) = s + (α / 5) * (1 - s) := by
    field_simp
  have h2 : (α / 5) * (1 - s) ≤ α := by nlinarith [hs, hs1, hα]
  have hnum : s ^ (1 - α / 5) ≤ α + s := by
    rw [hpow, hrhs] at hb'
    linarith
  have hden : 0 < α + s := by linarith
  rw [div_le_iff₀ hden]
  linarith

end Work.FTS.PhiStar.Psi0Est

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open scoped Real

/-- **The taper arithmetic.**  For `0 < a ≤ ℓ` and `N ≥ 1`,
`√(ℓ³/uvRad ℓ N) ≤ √(2/π)·(a^{-3/2}+1)·ℓ³·√ℓ/√N`.

With `uvRad ℓ N = πN/(2ℓ)` the left side is exactly
`√(2ℓ⁴/(πN)) = √(2/π)·ℓ²/√N`, while `a ≤ ℓ` forces `a^{-3/2} ≥ ℓ^{-3/2}`, so the right side
dominates `√(2/π)·ℓ^{-3/2}·ℓ³·√ℓ/√N = √(2/π)·ℓ²/√N`.  The two sides agree at `a = ℓ`. -/
theorem taperArith {ℓ a : ℝ} {N : ℕ} (hℓ : 0 < ℓ) (ha : 0 < a) (hℓa : a ≤ ℓ) (hN : 1 ≤ N) :
    Real.sqrt (ℓ ^ 3 / Work.BoseBoxFock.uvRad ℓ N)
      ≤ Real.sqrt (2 / Real.pi) * (a ^ (-(3 / 2 : ℝ)) + 1) * ℓ ^ 3 * Real.sqrt ℓ
          / Real.sqrt (N : ℝ) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hC : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  -- `uvRad ℓ N = πN/(2ℓ)`.
  have huvRad : Work.BoseBoxFock.uvRad ℓ N = Real.pi * (N : ℝ) / (2 * ℓ) := by
    rw [Work.BoseBoxFock.uvRad]; ring
  -- The left side is exactly `√(2/π)·ℓ²/√N`.
  have hLHS : Real.sqrt (ℓ ^ 3 / Work.BoseBoxFock.uvRad ℓ N)
      = Real.sqrt (2 / Real.pi) * ℓ ^ 2 / Real.sqrt (N : ℝ) := by
    rw [huvRad]
    have harg : ℓ ^ 3 / (Real.pi * (N : ℝ) / (2 * ℓ))
        = 2 * ℓ ^ 4 / (Real.pi * (N : ℝ)) := by
      field_simp
    rw [harg]
    rw [Real.sqrt_div (by positivity) (Real.pi * (N : ℝ))]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (ℓ ^ 4)]
    rw [show Real.sqrt (ℓ ^ 4) = ℓ ^ 2 by
      rw [show ℓ ^ 4 = (ℓ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
    rw [Real.sqrt_mul (le_of_lt hπ) (N : ℝ)]
    rw [show Real.sqrt 2 * ℓ ^ 2 / (Real.sqrt Real.pi * Real.sqrt (N : ℝ))
        = (Real.sqrt 2 / Real.sqrt Real.pi) * ℓ ^ 2 / Real.sqrt (N : ℝ) by ring]
    rw [← Real.sqrt_div (show (0 : ℝ) ≤ 2 by norm_num) Real.pi]
  -- `ℓ^{-3/2}·ℓ³·√ℓ = ℓ²`.
  have hprod : ℓ ^ (-(3 / 2) : ℝ) * ℓ ^ 3 * Real.sqrt ℓ = ℓ ^ 2 := by
    rw [Real.sqrt_eq_rpow]
    rw [show ℓ ^ 3 = ℓ ^ (3 : ℝ) by exact (Real.rpow_natCast ℓ 3).symm]
    rw [show ℓ ^ 2 = ℓ ^ (2 : ℝ) by exact (Real.rpow_natCast ℓ 2).symm]
    rw [mul_assoc, ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
    norm_num
  -- `a^{-3/2} ≥ ℓ^{-3/2}` since `0 < a ≤ ℓ` and the exponent is negative.
  have ha_inv : ℓ ^ (-(3 / 2) : ℝ) ≤ a ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ha hℓa (by norm_num)
  calc Real.sqrt (ℓ ^ 3 / Work.BoseBoxFock.uvRad ℓ N)
      = Real.sqrt (2 / Real.pi) * ℓ ^ 2 / Real.sqrt (N : ℝ) := hLHS
    _ = Real.sqrt (2 / Real.pi) * ℓ ^ (-(3 / 2) : ℝ) * ℓ ^ 3 * Real.sqrt ℓ
          / Real.sqrt (N : ℝ) := by
        rw [← hprod]; ring
    _ ≤ Real.sqrt (2 / Real.pi) * (a ^ (-(3 / 2) : ℝ) + 1) * ℓ ^ 3 * Real.sqrt ℓ
          / Real.sqrt (N : ℝ) := by
        apply div_le_div_of_nonneg_right _ hsN.le
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg ℓ)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hC
        linarith

end Work.BoseBoxFock.PCFU

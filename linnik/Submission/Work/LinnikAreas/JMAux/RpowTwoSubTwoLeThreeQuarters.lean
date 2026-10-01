import Mathlib

namespace Work.LinnikAreas.JMAux

/-- For `θ ≤ 11/10`, the quantity `2 ^ (θ - 2)` is at most `3/4`.
    Indeed `2 ^ (θ - 2) ≤ 2 ^ (-(9/10)) ≤ 2 ^ (-(1/2)) = 1/√2 ≤ 3/4`. -/
lemma RpowTwoSubTwoLeThreeQuarters {θ : ℝ} (hθ : θ ≤ 11/10) : (2:ℝ)^(θ - 2) ≤ 3/4 := by
  -- exponent comparison: `θ - 2 ≤ -(9/10)`
  have h1 : θ - 2 ≤ -(9/10:ℝ) := by linarith
  have hmid : (2:ℝ)^(θ - 2) ≤ (2:ℝ)^(-(9/10:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  -- it remains to bound the constant `2 ^ (-(9/10))`
  have hconst : (2:ℝ)^(-(9/10:ℝ)) ≤ 3/4 := by
    -- `2 ^ (-(9/10)) ≤ 2 ^ (-(1/2))` since the exponent is monotone (base `2 ≥ 1`)
    have h : (2:ℝ)^(-(9/10:ℝ)) ≤ (2:ℝ)^(-(1/2:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    -- `2 ^ (-(1/2)) = (√2)⁻¹`
    have hsqrt : (2:ℝ)^(-(1/2:ℝ)) = (Real.sqrt 2)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), ← Real.sqrt_eq_rpow 2]
    rw [hsqrt] at h
    -- `4/3 ≤ √2` because `(4/3)^2 = 16/9 ≤ 2`
    have hs : (4/3:ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt] <;> norm_num
    -- reciprocals reverse the inequality, and `(4/3)⁻¹ = 3/4`
    have hrec := inv_anti₀ (by norm_num : (0:ℝ) < 4/3) hs
    rw [show ((4/3:ℝ))⁻¹ = 3/4 by norm_num] at hrec
    exact h.trans hrec
  exact hmid.trans hconst

end Work.LinnikAreas.JMAux

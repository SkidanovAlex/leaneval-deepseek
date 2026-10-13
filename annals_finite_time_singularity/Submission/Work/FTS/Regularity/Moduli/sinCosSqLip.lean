import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity.Moduli

/-- `θ ↦ sin θ * cos θ ^ 2` is 3-Lipschitz on `ℝ` (its true Lipschitz constant is
`4√2/9 < 1`, but the crude bound `3` is what is needed). -/
lemma sinCosSqLip (θ θ' : ℝ) : |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ≤ 3 * |θ - θ'| := by
  have hsin : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := Real.abs_sin_sub_sin_le θ θ'
  have hcos : |Real.cos θ - Real.cos θ'| ≤ |θ - θ'| := Real.abs_cos_sub_cos_le θ θ'
  have hD : 0 ≤ |θ - θ'| := abs_nonneg _
  have hcos2 : |Real.cos θ ^ 2 - Real.cos θ' ^ 2| ≤ 2 * |θ - θ'| := by
    have hfac : Real.cos θ ^ 2 - Real.cos θ' ^ 2
        = (Real.cos θ - Real.cos θ') * (Real.cos θ + Real.cos θ') := by ring
    rw [hfac, abs_mul]
    have h2 : |Real.cos θ + Real.cos θ'| ≤ 2 := by
      have := abs_add_le (Real.cos θ) (Real.cos θ')
      have a1 := Real.abs_cos_le_one θ
      have a2 := Real.abs_cos_le_one θ'
      linarith
    calc |Real.cos θ - Real.cos θ'| * |Real.cos θ + Real.cos θ'|
        ≤ |θ - θ'| * 2 := mul_le_mul hcos h2 (abs_nonneg _) hD
      _ = 2 * |θ - θ'| := by ring
  have hsq : |Real.cos θ' ^ 2| ≤ 1 := by
    rw [abs_pow]
    nlinarith [Real.abs_cos_le_one θ', abs_nonneg (Real.cos θ')]
  have h1 : |Real.sin θ| * |Real.cos θ ^ 2 - Real.cos θ' ^ 2| ≤ 1 * (2 * |θ - θ'|) :=
    mul_le_mul (Real.abs_sin_le_one θ) hcos2 (abs_nonneg _) (by norm_num)
  have h2 : |Real.sin θ - Real.sin θ'| * |Real.cos θ' ^ 2| ≤ |θ - θ'| * 1 :=
    mul_le_mul hsin hsq (abs_nonneg _) hD
  calc |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2|
      = |Real.sin θ * (Real.cos θ ^ 2 - Real.cos θ' ^ 2)
          + (Real.sin θ - Real.sin θ') * Real.cos θ' ^ 2| := by
        congr 1; ring
    _ ≤ |Real.sin θ * (Real.cos θ ^ 2 - Real.cos θ' ^ 2)|
          + |(Real.sin θ - Real.sin θ') * Real.cos θ' ^ 2| := abs_add_le _ _
    _ = |Real.sin θ| * |Real.cos θ ^ 2 - Real.cos θ' ^ 2|
          + |Real.sin θ - Real.sin θ'| * |Real.cos θ' ^ 2| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (2 * |θ - θ'|) + |θ - θ'| * 1 := add_le_add h1 h2
    _ = 3 * |θ - θ'| := by ring

end Work.FTS.Regularity.Moduli

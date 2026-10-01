import Mathlib

set_option linter.unusedVariables false

namespace Work.LinnikAreas.RealZeroCount

/-- Arithmetic core: from the inequality `k / (3δ) ≤ 1/(2δ) + (C + log N + log2/2 + 3/2)`
together with `log N ≤ L` and `C + log2/2 + 3/2 ≤ L` one bounds `k ≤ 3/2 + 6·δ·L`. -/
theorem countArith {k δ t L N C : ℝ} (hδ : 0 < δ) (hδL : δ * L = t) (hL : 0 < L)
    (hN : Real.log N ≤ L) (hCL : C + Real.log 2 / 2 + 3 / 2 ≤ L)
    (hkey : k * (1 / (3 * δ)) ≤ 1 / (2 * δ) + C + Real.log N + Real.log 2 / 2 + 3 / 2) :
    k ≤ 3 / 2 + 6 * t := by
  have h3δ : (0:ℝ) < 3 * δ := by linarith
  -- regroup the right-hand side of `hkey`
  have hR : (1 / (2 * δ) + C + Real.log N + Real.log 2 / 2 + 3 / 2 : ℝ)
      = 1 / (2 * δ) + (C + Real.log N + Real.log 2 / 2 + 3 / 2) := by ring
  have hkey' : k * (1 / (3 * δ))
      ≤ 1 / (2 * δ) + (C + Real.log N + Real.log 2 / 2 + 3 / 2) := by
    rw [hR] at hkey; exact hkey
  -- multiply `hkey'` through by `3δ > 0`
  have hb1 : k ≤ 3 * δ * (1 / (2 * δ) + (C + Real.log N + Real.log 2 / 2 + 3 / 2)) := by
    have := mul_le_mul_of_nonneg_left hkey' (le_of_lt h3δ)
    have hk : 3 * δ * (k * (1 / (3 * δ))) = k := by field_simp
    linarith
  -- `3δ · (1/(2δ) + B) = 3/2 + 3δ·B`
  have hsplit : 3 * δ * (1 / (2 * δ) + (C + Real.log N + Real.log 2 / 2 + 3 / 2))
      = 3 / 2 + 3 * δ * (C + Real.log N + Real.log 2 / 2 + 3 / 2) := by
    have e : 3 * δ * (1 / (2 * δ)) = 3 / 2 := by rw [mul_one_div]; field_simp
    calc 3 * δ * (1 / (2 * δ) + (C + Real.log N + Real.log 2 / 2 + 3 / 2))
        = 3 * δ * (1 / (2 * δ)) + 3 * δ * (C + Real.log N + Real.log 2 / 2 + 3 / 2) := by ring
      _ = 3 / 2 + 3 * δ * (C + Real.log N + Real.log 2 / 2 + 3 / 2) := by rw [e]
  -- `C + log N + log2/2 + 3/2 ≤ 2L`, hence `3δ · B ≤ 6t`
  have hA : C + Real.log N + Real.log 2 / 2 + 3 / 2 ≤ 2 * L := by linarith
  have h4 : 3 * δ * (C + Real.log N + Real.log 2 / 2 + 3 / 2) ≤ 6 * t := by
    have h5 := mul_le_mul_of_nonneg_left hA (le_of_lt h3δ)
    calc 3 * δ * (C + Real.log N + Real.log 2 / 2 + 3 / 2) ≤ 3 * δ * (2 * L) := h5
      _ = 6 * (δ * L) := by ring
      _ = 6 * t := by rw [hδL]
  linarith

end Work.LinnikAreas.RealZeroCount

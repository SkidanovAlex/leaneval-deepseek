import Mathlib.Analysis.Real.Sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

/-- **Numeric Cauchy–Schwarz / AM–GM form.**  If `z` is bounded by the `l`-parametrised family
`l * A1 / 2 + B / (2 * l)` for every `l > 0`, with `0 ≤ A1 ≤ A` and `0 ≤ B`, then
`z ≤ √A √B`.

Indeed the family is minimal at `l = √(A1 * B) / A1`, where it equals `√(A1 * B)`; and
`√(A1 * B) ≤ √A √B` because `A1 * B ≤ A * B`. -/
theorem csNumeric {A A1 B z : ℝ} (hA1 : 0 ≤ A1) (hA1A : A1 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → z ≤ l * A1 / 2 + B / (2 * l)) :
    z ≤ Real.sqrt A * Real.sqrt B := by
  have hmain : z ≤ Real.sqrt (A1 * B) := by
    rcases eq_or_lt_of_le hA1 with h0 | hpos
    · -- `A1 = 0`: the bound forces `z ≤ 0`
      subst h0
      have hz : z ≤ 0 := by
        by_contra hc
        push Not at hc
        rcases eq_or_lt_of_le hB with hB0 | hBpos
        · subst hB0
          have hh := h 1 (by norm_num)
          norm_num at hh
          linarith
        · have hl : 0 < B / z := div_pos hBpos hc
          have hh := h (B / z) hl
          have hsimp : B / (2 * (B / z)) = z / 2 := by field_simp
          rw [hsimp] at hh
          linarith
      simpa using hz
    · rcases eq_or_lt_of_le hB with hB0 | hBpos
      · -- `B = 0`: the bound forces `z ≤ 0`
        subst hB0
        have hz : z ≤ 0 := by
          by_contra hc
          push Not at hc
          have hl : 0 < z / A1 := div_pos hc hpos
          have hh := h (z / A1) hl
          have h1 : (z / A1) * A1 / 2 = z / 2 := by
            rw [div_mul_cancel₀ z (ne_of_gt hpos)]
          rw [h1] at hh
          norm_num at hh
          linarith
        simpa using hz
      · -- `0 < A1` and `0 < B`: evaluate at the optimal `l = √(A1 * B) / A1`
        set s := Real.sqrt (A1 * B) with hs
        have hspos : 0 < s := Real.sqrt_pos_of_pos (mul_pos hpos hBpos)
        have hl : 0 < s / A1 := div_pos hspos hpos
        have hh := h (s / A1) hl
        have h1 : (s / A1) * A1 / 2 = s / 2 := by
          rw [div_mul_cancel₀ s (ne_of_gt hpos)]
        have h2 : B / (2 * (s / A1)) = s / 2 := by
          have hsq : s ^ 2 = A1 * B := Real.sq_sqrt (mul_nonneg hpos.le hBpos.le)
          field_simp
          nlinarith [hsq]
        rw [h1, h2] at hh
        linarith
  calc z ≤ Real.sqrt (A1 * B) := hmain
    _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hA1A hB)
    _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul (le_trans hA1 hA1A) B

end Work.FTS.EllSol

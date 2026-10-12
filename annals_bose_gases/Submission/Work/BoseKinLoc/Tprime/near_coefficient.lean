import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Tprime

/-
Coefficient bookkeeping for the `T'` residual.

For every quadruple of (coupling) constants `K₃ K₄ K₅ M` there is a constant `C ≥ 1`,
depending only on them, such that for all `C₀ ≥ 6` and all `0 ≤ x ≤ (5/6)C₀`

  K₄/C₀⁵ · (9/64)x⁴ + 4(2π)⁻³ (K₅/(C₀/6)⁶) x² + 2(2π)⁻³ (M x² K₃/C₀³) ≤ C · x²/C₀³.

The estimate is elementary: every summand already carries a factor `x²`, and each of the
three `C₀`-dependent factors is `O(1/C₀³)` on the range in question:
* `9/64 · x²/C₀⁵ ≤ 9/64 · (25/36)/C₀³ = (25/256)/C₀³`, since `x ≤ (5/6)C₀`,
* `1/(C₀/6)⁶ = 6⁶/C₀⁶ ≤ 216/C₀³`, since `C₀³ ≥ 216`,
* `1/C₀³` is already of the required shape.

`C` is chosen as `1 + 25/256·|K₄| + 864·(2π)⁻³·|K₅| + 2·(2π)⁻³·|M·K₃|`.
-/
theorem near_coefficient (K₃ K₄ K₅ M : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ C₀ x : ℝ, 6 ≤ C₀ → 0 ≤ x → x ≤ 5 / 6 * C₀ →
      K₄ / C₀ ^ 5 * ((9 / 64) * x ^ 4)
        + 4 * ((2 * Real.pi) ^ 3)⁻¹ * (K₅ / ((C₀ / 6) ^ 6)) * x ^ 2
        + 2 * ((2 * Real.pi) ^ 3)⁻¹ * (M * x ^ 2 * (K₃ / C₀ ^ 3))
        ≤ C * ((C₀ ^ 3)⁻¹) * x ^ 2 := by
  refine ⟨1 + 25 / 256 * |K₄| + 864 * ((2 * Real.pi) ^ 3)⁻¹ * |K₅|
      + 2 * ((2 * Real.pi) ^ 3)⁻¹ * |M * K₃|, ?_, ?_⟩
  · have h₁ : 0 ≤ 25 / 256 * |K₄| := by positivity
    have h₂ : 0 ≤ 864 * ((2 * Real.pi) ^ 3)⁻¹ * |K₅| := by positivity
    have h₃ : 0 ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * |M * K₃| := by positivity
    linarith
  · intro C₀ x h1 h2 h3
    have hC0 : 0 < C₀ := by linarith
    have hp : 0 < ((2 * Real.pi) ^ 3)⁻¹ := inv_pos.mpr (by positivity)
    set p := ((2 * Real.pi) ^ 3)⁻¹ with hpdef
    have hp0 : 0 ≤ p := hp.le
    set C := 1 + 25 / 256 * |K₄| + 864 * p * |K₅| + 2 * p * |M * K₃| with hCdef
    -- nonnegativity of the reference monomial
    have hX : 0 ≤ x ^ 2 * C₀ ^ 3 := by positivity
    -- `C₀ ^ 3 ≥ 216`
    have hC0pow : (216 : ℝ) ≤ C₀ ^ 3 := by
      nlinarith [h1, sq_nonneg C₀, sq_nonneg (C₀ - 6)]
    -- `x ^ 2 ≤ (25/36) C₀ ^ 2`, hence `x ^ 4 * C₀ ≤ (25/36) x ^ 2 * C₀ ^ 3`
    have hx2 : x ^ 2 ≤ 25 / 36 * C₀ ^ 2 := by nlinarith
    have hx4 : x ^ 4 * C₀ ≤ 25 / 36 * (x ^ 2 * C₀ ^ 3) := by
      have h : x ^ 2 * (x ^ 2 * C₀) ≤ (25 / 36 * C₀ ^ 2) * (x ^ 2 * C₀) :=
        mul_le_mul_of_nonneg_right hx2 (by positivity)
      calc x ^ 4 * C₀ = x ^ 2 * (x ^ 2 * C₀) := by ring
        _ ≤ (25 / 36 * C₀ ^ 2) * (x ^ 2 * C₀) := h
        _ = 25 / 36 * (x ^ 2 * C₀ ^ 3) := by ring
    -- first summand
    have hT1 : K₄ * (9 / 64) * (x ^ 4 * C₀) ≤ (25 / 256 * |K₄|) * (x ^ 2 * C₀ ^ 3) := by
      have hs1 : K₄ * (x ^ 4 * C₀) ≤ |K₄| * (x ^ 4 * C₀) :=
        mul_le_mul_of_nonneg_right (le_abs_self K₄) (by positivity)
      have hs2 : |K₄| * (x ^ 4 * C₀) ≤ |K₄| * (25 / 36 * (x ^ 2 * C₀ ^ 3)) :=
        mul_le_mul_of_nonneg_left hx4 (abs_nonneg K₄)
      calc K₄ * (9 / 64) * (x ^ 4 * C₀) = (9 / 64) * (K₄ * (x ^ 4 * C₀)) := by ring
        _ ≤ (9 / 64) * (|K₄| * (x ^ 4 * C₀)) := by
              apply mul_le_mul_of_nonneg_left hs1; norm_num
        _ ≤ (9 / 64) * (|K₄| * (25 / 36 * (x ^ 2 * C₀ ^ 3))) := by
              apply mul_le_mul_of_nonneg_left hs2; norm_num
        _ = (25 / 256 * |K₄|) * (x ^ 2 * C₀ ^ 3) := by ring
    -- second summand
    have hT2 : 46656 * (4 * p * K₅) * x ^ 2 ≤ (864 * p * |K₅|) * (x ^ 2 * C₀ ^ 3) := by
      have hK5 : 216 * K₅ ≤ |K₅| * C₀ ^ 3 := by
        have ha : 216 * K₅ ≤ 216 * |K₅| := by linarith [le_abs_self K₅]
        have hb : 216 * |K₅| ≤ C₀ ^ 3 * |K₅| :=
          mul_le_mul_of_nonneg_right hC0pow (abs_nonneg K₅)
        linarith
      calc 46656 * (4 * p * K₅) * x ^ 2 = (4 * p * x ^ 2) * (216 * (216 * K₅)) := by ring
        _ ≤ (4 * p * x ^ 2) * (216 * (|K₅| * C₀ ^ 3)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK5 (by norm_num))
                (by positivity)
        _ = (864 * p * |K₅|) * (x ^ 2 * C₀ ^ 3) := by ring
    -- third summand
    have hT3 : 2 * p * (M * K₃) * (x ^ 2 * C₀ ^ 3) ≤ (2 * p * |M * K₃|) * (x ^ 2 * C₀ ^ 3) := by
      have h := mul_le_mul_of_nonneg_right (le_abs_self (M * K₃)) hX
      calc 2 * p * (M * K₃) * (x ^ 2 * C₀ ^ 3) = (2 * p) * ((M * K₃) * (x ^ 2 * C₀ ^ 3)) := by ring
        _ ≤ (2 * p) * (|M * K₃| * (x ^ 2 * C₀ ^ 3)) := by
              apply mul_le_mul_of_nonneg_left h; linarith
        _ = (2 * p * |M * K₃|) * (x ^ 2 * C₀ ^ 3) := by ring
    have hC : 25 / 256 * |K₄| + 864 * p * |K₅| + 2 * p * |M * K₃| ≤ C := by
      rw [hCdef]; linarith
    -- clear the `C₀`-denominators: multiply by `C₀ ^ 6 > 0`
    have eL : C₀ ^ 6 * (K₄ / C₀ ^ 5 * ((9 / 64) * x ^ 4)
        + 4 * p * (K₅ / ((C₀ / 6) ^ 6)) * x ^ 2
        + 2 * p * (M * x ^ 2 * (K₃ / C₀ ^ 3)))
        = K₄ * (9 / 64) * (x ^ 4 * C₀) + 46656 * (4 * p * K₅) * x ^ 2
          + 2 * p * (M * K₃) * (x ^ 2 * C₀ ^ 3) := by
      field_simp <;> ring
    have eR : C₀ ^ 6 * (C * ((C₀ ^ 3)⁻¹) * x ^ 2) = C * (x ^ 2 * C₀ ^ 3) := by
      field_simp
    suffices hmain : C₀ ^ 6 * (K₄ / C₀ ^ 5 * ((9 / 64) * x ^ 4)
        + 4 * p * (K₅ / ((C₀ / 6) ^ 6)) * x ^ 2
        + 2 * p * (M * x ^ 2 * (K₃ / C₀ ^ 3)))
        ≤ C₀ ^ 6 * (C * ((C₀ ^ 3)⁻¹) * x ^ 2) by
      exact le_of_mul_le_mul_left hmain (pow_pos hC0 6)
    rw [eL, eR]
    calc K₄ * (9 / 64) * (x ^ 4 * C₀) + 46656 * (4 * p * K₅) * x ^ 2
          + 2 * p * (M * K₃) * (x ^ 2 * C₀ ^ 3)
        ≤ (25 / 256 * |K₄|) * (x ^ 2 * C₀ ^ 3) + (864 * p * |K₅|) * (x ^ 2 * C₀ ^ 3)
          + (2 * p * |M * K₃|) * (x ^ 2 * C₀ ^ 3) :=
          add_le_add (add_le_add hT1 hT2) hT3
      _ = (25 / 256 * |K₄| + 864 * p * |K₅| + 2 * p * |M * K₃|) * (x ^ 2 * C₀ ^ 3) := by ring
      _ ≤ C * (x ^ 2 * C₀ ^ 3) := mul_le_mul_of_nonneg_right hC hX

end Work.BoseKinLoc.Tprime

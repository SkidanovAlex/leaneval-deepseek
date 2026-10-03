import Mathlib

namespace Work.KMTAreas.SupNorm

/-- Elementary arithmetic bound used in the sup-norm estimates: for `0 ≤ ν, C₁, C₂, ηᵢ`
and `0 < δ ≤ 1`,
`ν δ η₀ + C₁ δ η₀ + ν η₁ + C₂ δ η₀ + 2 C₁ η₁ + ν η₂ / δ`
is bounded by `(η₀ + η₁ + η₂ + C₁ η₀ + C₂ η₀ + 2 C₁ η₁) * (ν / δ + 1)`.

The point is that every term of the left-hand side is dominated either by a term of
`(ν/δ)·(η₀+η₁+η₂)` (using `δ ≤ 1/δ`) or by a term of
`(C₁ η₀ + C₂ η₀ + 2 C₁ η₁)` (using `δ ≤ 1`). -/
theorem arith_bound {ν δ C₁ C₂ η0 η1 η2 : ℝ}
    (hν0 : 0 ≤ ν) (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη0 : 0 ≤ η0) (hη1 : 0 ≤ η1) (hη2 : 0 ≤ η2) :
    ν * δ * η0 + C₁ * δ * η0 + ν * η1 + C₂ * δ * η0 + 2 * C₁ * η1 + ν * η2 / δ
      ≤ (η0 + η1 + η2 + C₁ * η0 + C₂ * η0 + 2 * C₁ * η1) * (ν / δ + 1) := by
  -- `δ ≤ 1/δ` and `1 ≤ 1/δ`, both equivalent to `δ * δ ≤ 1` resp. `δ ≤ 1`.
  have hδle : δ ≤ 1 / δ := by rw [le_div_iff₀ hδ]; nlinarith
  have h1inv : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hνδ0 : (0 : ℝ) ≤ ν / δ := by positivity
  -- the `ν`-terms are dominated by `(ν/δ) * (η₀+η₁+η₂)`
  have h1 : ν * δ * η0 ≤ (ν / δ) * η0 := by
    have h : (ν * η0) * δ ≤ (ν * η0) * (1 / δ) :=
      mul_le_mul_of_nonneg_left hδle (mul_nonneg hν0 hη0)
    calc ν * δ * η0 = (ν * η0) * δ := by ring
      _ ≤ (ν * η0) * (1 / δ) := h
      _ = (ν / δ) * η0 := by ring
  have h2 : ν * η1 ≤ (ν / δ) * η1 := by
    have h : (ν * η1) * 1 ≤ (ν * η1) * (1 / δ) :=
      mul_le_mul_of_nonneg_left h1inv (mul_nonneg hν0 hη1)
    calc ν * η1 = (ν * η1) * 1 := by ring
      _ ≤ (ν * η1) * (1 / δ) := h
      _ = (ν / δ) * η1 := by ring
  have h3 : ν * η2 / δ ≤ (ν / δ) * η2 := by
    have he : ν * η2 / δ = (ν / δ) * η2 := by ring
    linarith
  have hkey : ν * δ * η0 + ν * η1 + ν * η2 / δ
      ≤ (ν / δ) * η0 + (ν / δ) * η1 + (ν / δ) * η2 := by linarith [h1, h2, h3]
  -- the `C`-terms are dominated by `C₁ η₀ + C₂ η₀ + 2 C₁ η₁`
  have hCt : C₁ * δ * η0 + C₂ * δ * η0 + 2 * C₁ * η1 ≤ C₁ * η0 + C₂ * η0 + 2 * C₁ * η1 := by
    have hC1δ : C₁ * δ * η0 ≤ C₁ * η0 := by
      have h : δ * η0 ≤ 1 * η0 := mul_le_mul_of_nonneg_right hδ1 hη0
      calc C₁ * δ * η0 = C₁ * (δ * η0) := by ring
        _ ≤ C₁ * (1 * η0) := mul_le_mul_of_nonneg_left h hC₁0
        _ = C₁ * η0 := by ring
    have hC2δ : C₂ * δ * η0 ≤ C₂ * η0 := by
      have h : δ * η0 ≤ 1 * η0 := mul_le_mul_of_nonneg_right hδ1 hη0
      calc C₂ * δ * η0 = C₂ * (δ * η0) := by ring
        _ ≤ C₂ * (1 * η0) := mul_le_mul_of_nonneg_left h hC₂0
        _ = C₂ * η0 := by ring
    linarith [hC1δ, hC2δ]
  have hT : (0 : ℝ) ≤ η0 + η1 + η2 := by linarith
  have hU : (0 : ℝ) ≤ C₁ * η0 + C₂ * η0 + 2 * C₁ * η1 := by
    have hA : 0 ≤ C₁ * η0 := mul_nonneg hC₁0 hη0
    have hB : 0 ≤ C₂ * η0 := mul_nonneg hC₂0 hη0
    have hC : 0 ≤ 2 * C₁ * η1 := by nlinarith [mul_nonneg hC₁0 hη1]
    linarith
  have hlast : (ν / δ) * (η0 + η1 + η2) + (C₁ * η0 + C₂ * η0 + 2 * C₁ * η1)
      ≤ (η0 + η1 + η2 + C₁ * η0 + C₂ * η0 + 2 * C₁ * η1) * (ν / δ + 1) := by
    have hUC : 0 ≤ (C₁ * η0 + C₂ * η0 + 2 * C₁ * η1) * (ν / δ) := mul_nonneg hU hνδ0
    nlinarith [hUC, hT]
  calc ν * δ * η0 + C₁ * δ * η0 + ν * η1 + C₂ * δ * η0 + 2 * C₁ * η1 + ν * η2 / δ
      = (ν * δ * η0 + ν * η1 + ν * η2 / δ) + (C₁ * δ * η0 + C₂ * δ * η0 + 2 * C₁ * η1) := by ring
    _ ≤ ((ν / δ) * η0 + (ν / δ) * η1 + (ν / δ) * η2) + (C₁ * η0 + C₂ * η0 + 2 * C₁ * η1) :=
        add_le_add hkey hCt
    _ = (ν / δ) * (η0 + η1 + η2) + (C₁ * η0 + C₂ * η0 + 2 * C₁ * η1) := by ring
    _ ≤ _ := hlast

end Work.KMTAreas.SupNorm

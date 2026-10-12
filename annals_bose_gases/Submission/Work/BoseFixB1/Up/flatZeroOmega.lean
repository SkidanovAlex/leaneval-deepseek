import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000

/-!
# `Work.BoseFixB1.Up.flatZeroOmega` — the real arithmetic of the exactly-flat per-box bound

With `τ` the state's smooth density, `W₁ = w1MassB`, `W₂ = flatPairMass`, `κ = chiMass`,
`A = boxMass`, `Y = Xp/N` the pair-condensate count per unit norm, `Dn = D/N` the diagonal
correction per unit norm, and `F₁(τ) = μ(τ−μ)²/(τ+μ)` the sharp `F`-weight, the exactly-flat bound
`PerBoxF` at coefficient `c₁` reduces to

    Ω := c₁W₁F₁(τ) + μW₁τ − ½μ²W₁ + ρ·Dn + (ρ − ½W₂)·Y − ρτ² ,    ρ := 4c₁W₁μ²/(τ+μ)²,

together with the two state-level facts `Y ≥ τ² − τ/A` (the pair-condensate Cauchy–Schwarz,
`Work.BoseFixB1Up.flatPairJensen`) and `Dn ≤ Cχ²τ/κ` (the diagonal count bound, `Cχ` a bound for
the cutoff).  This lemma is the pure-real part: it bounds `Ω` by the *linear* scale `μ`, which is
what the error bracket `err ≥ μ(a v)` pays.

The proof is the completion of squares `c₁F₁(τ) + μτ − ½μ² = ½τ² + (τ−μ)²(c₁μ/(τ+μ) − ½)`: the
quadratic `−½W₂τ²` of the pair-condensate damping cancels `½W₁τ²` (using `W₁ ≤ W₂`), and the
remaining linear/constant pieces are bounded by a crude completion of squares.
-/

namespace Work.BoseFixB1.Up

/-- **The real arithmetic of the exactly-flat branch.** -/
theorem flatZeroOmega_le {μ W₁ W₂ κ A τ Y Dn Cχ c₁ : ℝ}
    (hμ : 0 < μ) (hW₁ : 0 ≤ W₁) (hW : W₁ ≤ W₂) (hW₂ : 0 ≤ W₂) (hA : 0 < A) (hτ : 0 ≤ τ)
    (hκ : 0 ≤ κ) (hCχ : 0 ≤ Cχ) (hDnn : 0 ≤ Dn) (hDnle : Dn ≤ Cχ ^ 2 * τ / κ)
    (hc₁ : 0 < c₁) (hc₁4 : c₁ ≤ 1 / 4) (hc₁8 : 8 * c₁ * W₁ ≤ W₂)
    (hY : τ ^ 2 - τ / A ≤ Y) :
    c₁ * W₁ * (μ * (τ - μ) ^ 2 / (τ + μ)) + μ * W₁ * τ - (1 / 2) * μ ^ 2 * W₁
      + (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * Dn
      + (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 - (1 / 2) * W₂) * Y
      - (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * τ ^ 2
      ≤ W₂ * μ / A + 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ + 3 * W₂ / (5 * A ^ 2)
        + c₁ * W₁ * Cχ ^ 2 * μ / κ := by
  have hτμ : 0 < τ + μ := by linarith
  have hden : (0:ℝ) < (τ + μ) ^ 2 := by positivity
  -- ## (1) the coefficient of `Y` is nonpositive
  have hρle : 4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 ≤ (1 / 2) * W₂ := by
    have h1 : 4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 ≤ 4 * c₁ * W₁ := by
      rw [div_le_iff₀ hden]
      have hμ2 : μ ^ 2 ≤ (τ + μ) ^ 2 := by nlinarith [hτ, hμ.le]
      exact mul_le_mul_of_nonneg_left hμ2 (by positivity)
    have h2 : 4 * c₁ * W₁ ≤ (1 / 2) * W₂ := by linarith [hc₁8]
    linarith
  have hYcoef : (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 - (1 / 2) * W₂) * Y
      ≤ (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 - (1 / 2) * W₂) * (τ ^ 2 - τ / A) :=
    mul_le_mul_of_nonpos_left hY (by linarith)
  have hρA : 0 ≤ (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * τ / A := by positivity
  have hYexp : (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 - (1 / 2) * W₂) * Y
      - (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * τ ^ 2
      ≤ -(1 / 2) * W₂ * τ ^ 2 + (1 / 2) * W₂ * τ / A := by
    have he : (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 - (1 / 2) * W₂) * (τ ^ 2 - τ / A)
        = (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * τ ^ 2
          - (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * τ / A
          - (1 / 2) * W₂ * τ ^ 2 + (1 / 2) * W₂ * τ / A := by ring
    linarith [hYcoef, he, hρA]
  -- ## (2) the diagonal term
  have hDnB : (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * Dn ≤ 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ := by
    have hCκ : 0 ≤ Cχ ^ 2 / κ := by positivity
    have h1 : (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * Dn
        ≤ (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * (Cχ ^ 2 * τ / κ) :=
      mul_le_mul_of_nonneg_left hDnle (by positivity)
    have h2 : (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * (Cχ ^ 2 * τ / κ)
        = (4 * c₁ * W₁ * μ ^ 2 * τ / (τ + μ) ^ 2) * (Cχ ^ 2 / κ) := by ring
    rw [h2] at h1
    have h3 : 4 * c₁ * W₁ * μ ^ 2 * τ / (τ + μ) ^ 2 ≤ (8 * c₁ * W₁) * μ := by
      rw [div_le_iff₀ hden]
      have hK : (0:ℝ) ≤ 4 * c₁ * W₁ := by positivity
      have hm : μ * τ ≤ 2 * (τ + μ) ^ 2 := by nlinarith [hτ, hμ.le]
      calc 4 * c₁ * W₁ * μ ^ 2 * τ = (4 * c₁ * W₁) * (μ * τ) * μ := by ring
        _ ≤ (4 * c₁ * W₁) * (2 * (τ + μ) ^ 2) * μ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hK) hμ.le
        _ = (8 * c₁ * W₁) * μ * (τ + μ) ^ 2 := by ring
    calc (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * Dn
        ≤ (4 * c₁ * W₁ * μ ^ 2 * τ / (τ + μ) ^ 2) * (Cχ ^ 2 / κ) := h1
      _ ≤ ((8 * c₁ * W₁) * μ) * (Cχ ^ 2 / κ) := mul_le_mul_of_nonneg_right h3 hCκ
      _ = 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ := by ring
  -- ## (3) the bulk
  have hid : c₁ * W₁ * (μ * (τ - μ) ^ 2 / (τ + μ)) + μ * W₁ * τ - (1 / 2) * μ ^ 2 * W₁
      = (1 / 2) * W₁ * τ ^ 2 + W₁ * (τ - μ) ^ 2 * (c₁ * μ / (τ + μ) - 1 / 2) := by
    field_simp
    ring
  have hbulk : (1 / 2) * W₁ * τ ^ 2 + W₁ * (τ - μ) ^ 2 * (c₁ * μ / (τ + μ) - 1 / 2)
      - (1 / 2) * W₂ * τ ^ 2 + (1 / 2) * W₂ * τ / A
      ≤ W₂ * μ / A + 3 * W₂ / (5 * A ^ 2) := by
    by_cases hcase : 2 * μ ≤ τ
    · -- `τ ≥ 2μ`
      have hb : W₁ * (τ - μ) ^ 2 * (c₁ * μ / (τ + μ) - 1 / 2)
          ≤ -((5 / 48) * W₁) * τ ^ 2 := by
        have hb1 : c₁ * μ / (τ + μ) - 1 / 2 ≤ -(5 / 12) := by
          have h1 : c₁ * μ / (τ + μ) ≤ c₁ / 3 := by
            rw [div_le_iff₀ hτμ]
            nlinarith [hcase, hc₁.le]
          linarith
        have hb2 : (τ / 2) ^ 2 ≤ (τ - μ) ^ 2 := by nlinarith [hcase]
        have hb3 : (τ - μ) ^ 2 * (c₁ * μ / (τ + μ) - 1 / 2)
            ≤ (τ - μ) ^ 2 * (-(5 / 12)) :=
          mul_le_mul_of_nonneg_left hb1 (sq_nonneg _)
        have hb4 : (τ - μ) ^ 2 * (-(5 / 12)) ≤ (τ / 2) ^ 2 * (-(5 / 12)) :=
          mul_le_mul_of_nonpos_right hb2 (by norm_num)
        have hb5 : (τ / 2) ^ 2 * (-(5 / 12)) = -(5 / 48) * τ ^ 2 := by ring
        have hle := mul_le_mul_of_nonneg_left (le_trans hb3 hb4) hW₁
        rw [hb5] at hle
        linarith [hle]
      have hstep : (1 / 2) * W₁ * τ ^ 2 + W₁ * (τ - μ) ^ 2 * (c₁ * μ / (τ + μ) - 1 / 2)
          - (1 / 2) * W₂ * τ ^ 2 + (1 / 2) * W₂ * τ / A
          ≤ -((1 / 2) * (W₂ - W₁) + (5 / 48) * W₁) * τ ^ 2 + (1 / 2) * W₂ * τ / A := by
        linarith [hb, hW]
      have hquad : -((1 / 2) * (W₂ - W₁) + (5 / 48) * W₁) * τ ^ 2 + (1 / 2) * W₂ * τ / A
          ≤ 3 * W₂ / (5 * A ^ 2) := by
        have hA0 : (5 / 48) * W₂ ≤ (1 / 2) * (W₂ - W₁) + (5 / 48) * W₁ := by linarith
        have h1 : -((1 / 2) * (W₂ - W₁) + (5 / 48) * W₁) * τ ^ 2 ≤ -((5 / 48) * W₂) * τ ^ 2 := by
          nlinarith [hA0, sq_nonneg τ]
        have h2 : -((5 / 48) * W₂) * τ ^ 2 + (1 / 2) * W₂ * τ / A
            = -((5 / 48) * W₂) * (τ - 12 / (5 * A)) ^ 2 + 3 * W₂ / (5 * A ^ 2) := by
          field_simp
          ring
        have h3 : 0 ≤ ((5 / 48) * W₂) * (τ - 12 / (5 * A)) ^ 2 := by positivity
        linarith [h1, h2, h3]
      have hWμA : 0 ≤ W₂ * μ / A := by positivity
      linarith [hstep, hquad, hWμA]
    · -- `τ ≤ 2μ`
      have hτ2 : τ ≤ 2 * μ := le_of_not_ge hcase
      have hb : W₁ * (τ - μ) ^ 2 * (c₁ * μ / (τ + μ) - 1 / 2) ≤ 0 := by
        refine mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hW₁ (sq_nonneg _)) ?_
        have hm : c₁ * μ / (τ + μ) ≤ c₁ := by
          rw [div_le_iff₀ hτμ]; nlinarith [hc₁.le, hμ.le]
        linarith
      have h2 : (1 / 2) * W₁ * τ ^ 2 ≤ (1 / 2) * W₂ * τ ^ 2 := by nlinarith [hW, sq_nonneg τ]
      have hstep : (1 / 2) * W₁ * τ ^ 2 + W₁ * (τ - μ) ^ 2 * (c₁ * μ / (τ + μ) - 1 / 2)
          - (1 / 2) * W₂ * τ ^ 2 + (1 / 2) * W₂ * τ / A ≤ (1 / 2) * W₂ * τ / A := by
        linarith [hb, h2]
      have hτA : (1 / 2) * W₂ * τ / A ≤ W₂ * μ / A := by
        have h1 : (1 / 2) * W₂ * τ ≤ W₂ * μ := by nlinarith [hW₂, hτ2]
        exact div_le_div_of_nonneg_right h1 hA.le
      have h3 : (0:ℝ) ≤ 3 * W₂ / (5 * A ^ 2) := by positivity
      linarith [hstep, hτA, h3]
  -- ## (4) assembly
  have hLL : c₁ * W₁ * (μ * (τ - μ) ^ 2 / (τ + μ)) + μ * W₁ * τ - (1 / 2) * μ ^ 2 * W₁
      + (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * Dn
      + (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 - (1 / 2) * W₂) * Y
      - (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * τ ^ 2
      = ((1 / 2) * W₁ * τ ^ 2 + W₁ * (τ - μ) ^ 2 * (c₁ * μ / (τ + μ) - 1 / 2)
          - (1 / 2) * W₂ * τ ^ 2 + (1 / 2) * W₂ * τ / A)
        + (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * Dn
        + ((4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 - (1 / 2) * W₂) * Y
            - (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * τ ^ 2
            + (1 / 2) * W₂ * τ ^ 2 - (1 / 2) * W₂ * τ / A) := by
    rw [hid]
    ring
  have htail : (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 - (1 / 2) * W₂) * Y
      - (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * τ ^ 2
      + (1 / 2) * W₂ * τ ^ 2 - (1 / 2) * W₂ * τ / A ≤ 0 := by
    linarith [hYexp]
  have hpos : 0 ≤ c₁ * W₁ * Cχ ^ 2 * μ / κ := by positivity
  rw [hLL]
  linarith [hbulk, hDnB, htail, hpos]

end Work.BoseFixB1.Up

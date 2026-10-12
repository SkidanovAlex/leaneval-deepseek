import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Assembly

/-- First slack condition: `εT + b/β² + 8*C*s³ ≤ 1`. -/
private lemma slack_p1 (β C c₀ s εT b : ℝ) (hβ : 0 < β) (hC : 0 < C)
    (hc₁ : c₀ ≤ 1 / 4) (hc₂ : c₀ ≤ β ^ 2 / 4) (hc₃ : 8 * C * c₀ ^ 3 ≤ 1 / 4)
    (hs : 0 < s) (hsc : s ≤ c₀) (hεc : εT ≤ c₀) (hb : 0 ≤ b) (hbc : b ≤ c₀) :
    εT + b / β ^ 2 + 8 * C * s ^ 3 ≤ 1 := by
  have hβ2 : (0 : ℝ) < β ^ 2 := pow_pos hβ 2
  have h1a : b / β ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hβ2]
    nlinarith [hbc, hc₂]
  have hs3 : s ^ 3 ≤ c₀ ^ 3 := pow_le_pow_left₀ (le_of_lt hs) hsc 3
  have h1b : 8 * C * s ^ 3 ≤ 1 / 4 := by nlinarith [hs3, hC, hc₃]
  linarith [h1a, h1b, hεc, hc₁, hb]

/-- Second slack condition. -/
private lemma slack_p2 (β C c₀ d s εT b : ℝ) (hβ : 0 < β) (hC : 0 < C) (hc₀ : 0 < c₀)
    (hc₁ : c₀ ≤ 1 / 4) (hc₃ : 8 * C * c₀ ^ 3 ≤ 1 / 4)
    (hc₄ : 128 * c₀ ^ 3 ≤ 7 * β) (hc₅ : (1600 / 9) * C * c₀ ^ 5 ≤ 7)
    (hdc : d ≤ c₀) (hs : 0 < s) (hsc : s ≤ c₀)
    (hε : 0 ≤ εT) (hεc : εT ≤ c₀) (hbc : b ≤ c₀) :
    b * β⁻¹ + εT * ((25 / 18) * C * d * s) ≤ (1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2) := by
  have hs2 : s ^ 2 ≤ c₀ ^ 2 := pow_le_pow_left₀ (le_of_lt hs) hsc 2
  have hbs : b * s ^ 2 ≤ c₀ ^ 3 := by
    have := mul_le_mul hbc hs2 (sq_nonneg s) (le_of_lt hc₀)
    nlinarith [this]
  have h2a : 48 * b * s ^ 2 ≤ 21 / 8 * β := by nlinarith [hbs, hc₄]
  have hC3 : C * c₀ ^ 3 ≤ 1 / 32 := by nlinarith [hc₃]
  have hs3 : s ^ 3 ≤ c₀ ^ 3 := pow_le_pow_left₀ (le_of_lt hs) hsc 3
  have hds : d * s ^ 3 ≤ c₀ ^ 4 := by
    have := mul_le_mul hdc hs3 (pow_nonneg (le_of_lt hs) 3) (le_of_lt hc₀)
    nlinarith [this]
  have hCd : C * d * s ^ 3 ≤ 1 / 128 := by nlinarith [hds, hC, hC3, hc₀, hc₁]
  have h2b : εT * (200 / 3) * C * d * β * s ^ 3 ≤ (25 / 48) * β * εT := by
    have hk : (0 : ℝ) ≤ (200 / 3) * (β * εT) :=
      mul_nonneg (by norm_num) (mul_nonneg (le_of_lt hβ) hε)
    have h := mul_le_mul_of_nonneg_right hCd hk
    nlinarith [h]
  have h2k : 48 * b * s ^ 2 + εT * (200 / 3) * C * d * β * s ^ 3 ≤ 7 * β * (1 - εT) := by
    nlinarith [h2a, h2b, hεc, hc₁, hc₅]
  have h2eq1 : b * β⁻¹ + εT * ((25 / 18) * C * d * s)
      = (48 * b * s ^ 2 + εT * (200 / 3) * C * d * β * s ^ 3) / (48 * β * s ^ 2) := by
    field_simp
    ring
  have h2eq2 : (1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2)
      = (7 * β * (1 - εT)) / (48 * β * s ^ 2) := by
    field_simp
    ring
  rw [h2eq1, h2eq2]
  exact div_le_div_of_nonneg_right h2k
    (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hβ)) (sq_nonneg s))

/-- Third slack condition. -/
private lemma slack_p3 (β c₀ d s εT b : ℝ) (hβ : 0 < β) (hc₀ : 0 < c₀)
    (hc₁ : c₀ ≤ 1 / 4) (hc₄ : 128 * c₀ ^ 3 ≤ 7 * β) (hc₆ : 48 * c₀ ^ 2 ≤ 7)
    (hd : 0 < d) (hs : 0 < s) (hsc : s ≤ c₀)
    (hε : 0 ≤ εT) (hεc : εT ≤ c₀) (hbc : b ≤ c₀) :
    εT / d ^ 2 + b * β⁻¹
      ≤ (1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2)
        + εT * ((7 / 3) * ((4 * (d * s))⁻¹) ^ 2) := by
  have hs2 : s ^ 2 ≤ c₀ ^ 2 := pow_le_pow_left₀ (le_of_lt hs) hsc 2
  have hbs : b * s ^ 2 ≤ c₀ ^ 3 := by
    have := mul_le_mul hbc hs2 (sq_nonneg s) (le_of_lt hc₀)
    nlinarith [this]
  have h3a : 48 * β * εT * s ^ 2 ≤ 7 * β * εT := by
    have hk : (0 : ℝ) ≤ β * εT := mul_nonneg (le_of_lt hβ) hε
    have := mul_le_mul_of_nonneg_right hc₆ hk
    nlinarith [this, hs2, hk]
  have h3b1 : 48 * b * s ^ 2 ≤ 7 * β * (1 - εT) := by
    nlinarith [hbs, hc₄, hεc, hc₁, hβ]
  have h3b : 48 * b * d ^ 2 * s ^ 2 ≤ 7 * β * d ^ 2 * (1 - εT) := by
    have hd2 : (0 : ℝ) ≤ d ^ 2 := le_of_lt (pow_pos hd 2)
    have := mul_le_mul_of_nonneg_right h3b1 hd2
    nlinarith [this]
  have h3k : 48 * β * εT * s ^ 2 + 48 * b * d ^ 2 * s ^ 2
      ≤ 7 * β * d ^ 2 * (1 - εT) + 7 * β * εT := by linarith [h3a, h3b]
  have h3eq1 : εT / d ^ 2 + b * β⁻¹
      = (48 * β * εT * s ^ 2 + 48 * b * d ^ 2 * s ^ 2) / (48 * β * d ^ 2 * s ^ 2) := by
    field_simp
  have h3eq2 : (1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2) + εT * ((7 / 3) * ((4 * (d * s))⁻¹) ^ 2)
      = (7 * β * d ^ 2 * (1 - εT) + 7 * β * εT) / (48 * β * d ^ 2 * s ^ 2) := by
    field_simp
    ring
  rw [h3eq1, h3eq2]
  exact div_le_div_of_nonneg_right h3k
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hβ)) (sq_nonneg d)) (sq_nonneg s))

theorem slack_conditions (β C c₀ d s εT b : ℝ) (hβ : 0 < β) (hC : 0 < C) (hc₀ : 0 < c₀)
    (hc₁ : c₀ ≤ 1 / 4) (hc₂ : c₀ ≤ β ^ 2 / 4) (hc₃ : 8 * C * c₀ ^ 3 ≤ 1 / 4)
    (hc₄ : 128 * c₀ ^ 3 ≤ 7 * β) (hc₅ : (1600 / 9) * C * c₀ ^ 5 ≤ 7) (hc₆ : 48 * c₀ ^ 2 ≤ 7)
    (hd : 0 < d) (hdc : d ≤ c₀) (hs : 0 < s) (hsc : s ≤ c₀)
    (hε : 0 ≤ εT) (hεc : εT ≤ c₀) (hb : 0 ≤ b) (hbc : b ≤ c₀) :
    (εT + b / β ^ 2 + 8 * C * s ^ 3 ≤ 1)
      ∧ (b * β⁻¹ + εT * ((25 / 18) * C * d * s) ≤ (1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2))
      ∧ (εT / d ^ 2 + b * β⁻¹
          ≤ (1 - εT) * ((7 / 3) * ((4 * s)⁻¹) ^ 2)
            + εT * ((7 / 3) * ((4 * (d * s))⁻¹) ^ 2)) :=
  ⟨slack_p1 β C c₀ s εT b hβ hC hc₁ hc₂ hc₃ hs hsc hεc hb hbc,
   slack_p2 β C c₀ d s εT b hβ hC hc₀ hc₁ hc₃ hc₄ hc₅ hdc hs hsc hε hεc hbc,
   slack_p3 β c₀ d s εT b hβ hc₀ hc₁ hc₄ hc₆ hd hs hsc hε hεc hbc⟩

end Work.BoseKinLoc.Assembly

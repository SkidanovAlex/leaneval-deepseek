import Mathlib

namespace Work.Prop36SW

/-- **The threshold of the round from the régime.**

If `c₀·η^{e₀} ≤ γ` and `Cn·(4/(3c₀))^{Mn} ≤ η^{M₀}·H` with `e₀·Mn ≤ M₀`, `0 < η ≤ 1`,
`0 < c₀`, `0 < γ`, then `Cn·(3γ/4)^{-Mn} ≤ H`.

The mathematics: `(3γ/4)^{-Mn} = (4/3)^{Mn}·γ^{-Mn}`, and `c₀^{Mn}·η^{M₀} ≤ γ^{Mn}` (from the
monomial régime `c₀·η^{e₀} ≤ γ` raised to the `Mn` and `η^{M₀} ≤ 1`), so multiplying the
hypothesis by `γ^{-Mn}` and using `γ^{Mn}·γ^{-Mn} = 1` gives the claim. -/
theorem reachStepAuxThreshold {Cn c₀ γ η H : ℝ} {e₀ Mn M₀ : ℕ}
    (hCn : 0 < Cn) (hc₀ : 0 < c₀) (hη0 : 0 < η) (hη1 : η ≤ 1) (hγ0 : 0 < γ)
    (hmon : c₀ * η ^ e₀ ≤ γ) (hk : e₀ * Mn ≤ M₀)
    (h : Cn * (4 / (3 * c₀)) ^ Mn ≤ η ^ M₀ * H) :
    Cn * (3 * γ / 4) ^ (-(Mn : ℤ)) ≤ H := by
  have hηe0 : (0 : ℝ) < η ^ e₀ := pow_pos hη0 _
  have hγnn : (0 : ℝ) ≤ γ := le_trans (mul_nonneg hc₀.le hηe0.le) hmon
  -- `H ≥ 0`
  have hLHSp : 0 < Cn * (4 / (3 * c₀)) ^ Mn :=
    mul_pos hCn (pow_pos (div_pos (by norm_num) (by positivity)) _)
  have hηM0 : (0 : ℝ) < η ^ M₀ := pow_pos hη0 _
  have hH0 : 0 ≤ H := by
    have h' : 0 ≤ η ^ M₀ * H := le_trans hLHSp.le h
    exact (mul_nonneg_iff_of_pos_left hηM0).mp h'
  -- `c₀^{Mn}·η^{M₀} ≤ γ^{Mn}`
  have hsplit1 : η ^ M₀ = η ^ (e₀ * Mn) * η ^ (M₀ - e₀ * Mn) := by
    rw [← pow_add]
    congr 1
    omega
  have hsplit2 : (c₀ * η ^ e₀) ^ Mn = c₀ ^ Mn * η ^ (e₀ * Mn) := by
    rw [mul_pow, ← pow_mul]
  have hsplit : c₀ ^ Mn * η ^ M₀ = (c₀ * η ^ e₀) ^ Mn * η ^ (M₀ - e₀ * Mn) := by
    rw [hsplit1, hsplit2]; ring
  have hpow : (c₀ * η ^ e₀) ^ Mn ≤ γ ^ Mn :=
    pow_le_pow_left₀ (mul_nonneg hc₀.le hηe0.le) hmon Mn
  have heta : η ^ (M₀ - e₀ * Mn) ≤ 1 := pow_le_one₀ hη0.le hη1
  have hc0Mn : c₀ ^ Mn * η ^ M₀ ≤ γ ^ Mn := by
    rw [hsplit]
    calc (c₀ * η ^ e₀) ^ Mn * η ^ (M₀ - e₀ * Mn)
        ≤ γ ^ Mn * 1 :=
          mul_le_mul hpow heta (pow_nonneg hη0.le _) (pow_nonneg hγnn _)
      _ = γ ^ Mn := mul_one _
  -- `Cn·(4/3)^{Mn} ≤ γ^{Mn}·H`
  have hA : Cn * (4 / (3 * c₀)) ^ Mn * c₀ ^ Mn = Cn * (4 / 3) ^ Mn := by
    rw [mul_assoc, ← mul_pow]
    congr 1
    field_simp
  have hCn34 : Cn * (4 / 3) ^ Mn ≤ γ ^ Mn * H := by
    have h1 := mul_le_mul_of_nonneg_right h (pow_nonneg hc₀.le Mn)
    rw [hA] at h1
    have h2 : (η ^ M₀ * H) * c₀ ^ Mn = c₀ ^ Mn * η ^ M₀ * H := by ring
    rw [h2] at h1
    have h3 : c₀ ^ Mn * η ^ M₀ * H ≤ γ ^ Mn * H :=
      mul_le_mul_of_nonneg_right hc0Mn hH0
    linarith
  -- the `zpow` identity
  have hkey : (3 * γ / 4) ^ (-(Mn : ℤ)) = (4 / 3) ^ Mn * γ ^ (-(Mn : ℤ)) := by
    have hγne : γ ≠ 0 := ne_of_gt hγ0
    have h1 : (3 * γ / 4) ^ (-(Mn : ℤ)) = ((3 * γ / 4) ^ Mn)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have h2 : γ ^ (-(Mn : ℤ)) = (γ ^ Mn)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [h1, h2]
    rw [show (3 * γ / 4) ^ Mn = (3 * γ) ^ Mn / 4 ^ Mn by rw [div_pow]]
    rw [show (4 / 3 : ℝ) ^ Mn = 4 ^ Mn / 3 ^ Mn by rw [div_pow]]
    rw [inv_div]
    field_simp
    ring
  have hgg : γ ^ Mn * γ ^ (-(Mn : ℤ)) = 1 := by
    have h1 : γ ^ Mn = γ ^ ((Mn : ℤ)) := by rw [zpow_natCast]
    rw [h1, ← zpow_add₀ (ne_of_gt hγ0), add_neg_cancel, zpow_zero]
  rw [hkey]
  calc Cn * ((4 / 3) ^ Mn * γ ^ (-(Mn : ℤ)))
      = Cn * (4 / 3) ^ Mn * γ ^ (-(Mn : ℤ)) := by ring
    _ ≤ (γ ^ Mn * H) * γ ^ (-(Mn : ℤ)) :=
          mul_le_mul_of_nonneg_right hCn34 (by positivity)
    _ = H * (γ ^ Mn * γ ^ (-(Mn : ℤ))) := by ring
    _ = H := by rw [hgg, mul_one]

end Work.Prop36SW

import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- The two square roots appearing in the small-box ledger sum to at most one.

Mathematically the argument is a two-sided estimate:

* first term: `8 k μ V / (3 (S - 1)) ≤ 8 · 1.06 / (3 · 2.99) = 848/897 ≤ (0.97231)²`,
  using `k ≤ 1.06` and `2.99 μ V ≤ S - 1`;
* second term: using `Kw V ≤ 2 K a³/scl`, `n ≤ 2 Cn μ V`, `Q ≤ k W S/(2 Kg V a)` one gets
  `16 Kw n Q V² ≤ 32 K Cn a² μ k W S V /(scl Kg)`, whence dividing by `3 W (S² - S)` and using
  `S - 1 ≥ 2.99 μ V`,
  `t₂² ≤ 32 k Cn (K a²/scl) / (3 · 2.99 Kg)`; and `12000 Cn (1 + K a²/scl) ≤ Kg` gives
  `Cn (K a²/scl) ≤ Kg/12000`, so `t₂² ≤ 32 k /(12000 · 8.97) ≤ (1.06)/3363.75 ≤ (9/500)²`.

Finally `97231/100000 + 9/500 = 99031/100000 ≤ 1`. -/
theorem swhCruxSqrtSum {μ a V W S Q n Cn K scl Kw k Kg : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hV : 0 < V) (hW : 0 < W) (hS : 0 < S) (hQ : 0 ≤ Q)
    (hCn : 4 ≤ Cn) (hK : 0 ≤ K) (hscl : 0 < scl) (hKw0 : 0 ≤ Kw) (hKg : 0 < Kg)
    (hk0 : 0 < k) (hk1 : k ≤ 1.06)
    (hn : n ≤ 2 * Cn * μ * V)
    (hS1 : 2.99 * μ * V ≤ S - 1)
    (hQsm : Q ≤ k * W * S / (2 * Kg * V * a))
    (hKwV : Kw * V ≤ 2 * K * a ^ 3 / scl)
    (hKgbig : 12000 * Cn * (1 + K * a ^ 2 / scl) ≤ Kg) :
    Real.sqrt (8 * k * μ * V / (3 * (S - 1))) +
      Real.sqrt (16 * Kw * n * Q * V ^ 2 / (3 * W * (S ^ 2 - S))) ≤ 1 := by
  have hCn0 : 0 < Cn := by linarith
  have hμV : 0 < μ * V := mul_pos hμ hV
  have hS1pos : 0 < S - 1 := by nlinarith
  have hS2 : 0 < S ^ 2 - S := by nlinarith [mul_pos hS hS1pos]
  have hden1 : 0 < 3 * (S - 1) := by nlinarith
  have hden2 : 0 < 3 * W * (S ^ 2 - S) := by nlinarith [hS2, hW]
  -- the first square root
  have hsqrt1 : Real.sqrt (8 * k * μ * V / (3 * (S - 1))) ≤ 97231 / 100000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ hden1]
    nlinarith [hk1, hS1, hμV]
  -- the second square root
  have hsqrt2 : Real.sqrt (16 * Kw * n * Q * V ^ 2 / (3 * W * (S ^ 2 - S))) ≤ 9 / 500 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ hden2]
    -- bound the numerator: `Kw n Q V²`
    have hKwV' : Kw ≤ 2 * K * a ^ 3 / scl / V := by
      rw [le_div_iff₀ hV]; linarith [hKwV]
    have h1 : 16 * Kw * n * Q * V ^ 2 ≤ 16 * Kw * (2 * Cn * μ * V) * Q * V ^ 2 := by
      have h : (0 : ℝ) ≤ 16 * Kw * Q * V ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right hn h
      linarith [this]
    have h2 : 16 * Kw * (2 * Cn * μ * V) * Q * V ^ 2 ≤
        16 * (2 * K * a ^ 3 / scl / V) * (2 * Cn * μ * V) * Q * V ^ 2 := by
      have h : (0 : ℝ) ≤ 16 * (2 * Cn * μ * V) * Q * V ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right hKwV' h
      linarith [this]
    have h3 : 16 * (2 * K * a ^ 3 / scl / V) * (2 * Cn * μ * V) * Q * V ^ 2 ≤
        16 * (2 * K * a ^ 3 / scl / V) * (2 * Cn * μ * V) *
          (k * W * S / (2 * Kg * V * a)) * V ^ 2 := by
      have h : (0 : ℝ) ≤ 16 * (2 * K * a ^ 3 / scl / V) * (2 * Cn * μ * V) * V ^ 2 := by
        positivity
      have := mul_le_mul_of_nonneg_left hQsm h
      linarith [this]
    have heq : 16 * (2 * K * a ^ 3 / scl / V) * (2 * Cn * μ * V) *
          (k * W * S / (2 * Kg * V * a)) * V ^ 2
        = 32 * K * Cn * a ^ 2 * μ * k * W * S * V / (scl * Kg) := by
      field_simp
      ring
    have hkey : 16 * Kw * n * Q * V ^ 2 ≤ 32 * K * Cn * a ^ 2 * μ * k * W * S * V / (scl * Kg) := by
      rw [heq] at h3; linarith
    -- compare the resulting expression with the quadratic bound
    have hMnn : (0 : ℝ) ≤ Kg * scl * μ * W * S * V := by positivity
    have hA'' : 12000 * Cn * (K * a ^ 2 / scl) ≤ Kg := by nlinarith [hKgbig, hCn0]
    have hA : 12000 * Cn * (K * a ^ 2) ≤ Kg * scl := by
      have h := mul_le_mul_of_nonneg_right hA'' (le_of_lt hscl)
      have he : (12000 * Cn * (K * a ^ 2 / scl)) * scl = 12000 * Cn * (K * a ^ 2) := by
        field_simp
      linarith [h, he]
    have hs1 : 32 * K * Cn * a ^ 2 * μ * k * W * S * V ≤
        (32 / 12000) * (Kg * scl * μ * k * W * S * V) := by
      have h : (0 : ℝ) ≤ (32 / 12000) * (μ * k * W * S * V) := by positivity
      have := mul_le_mul_of_nonneg_right hA h
      linarith [this]
    have hs2 : (32 / 12000) * (Kg * scl * μ * k * W * S * V) ≤
        (32 / 12000) * (Kg * scl * (1.06) * μ * W * S * V) := by
      have h : (0 : ℝ) ≤ (32 / 12000) * (Kg * scl * μ * W * S * V) := by positivity
      have := mul_le_mul_of_nonneg_left hk1 h
      linarith [this]
    have hs3 : (32 / 12000) * (Kg * scl * (1.06) * μ * W * S * V) ≤
        (9 / 500) ^ 2 * (3 * 2.99) * (Kg * scl * μ * W * S * V) := by
      have hnum : ((32 : ℝ) / 12000) * 1.06 ≤ ((9 : ℝ) / 500) ^ 2 * (3 * 2.99) := by norm_num
      have := mul_le_mul_of_nonneg_right hnum hMnn
      linarith [this]
    have hs4 : (9 / 500) ^ 2 * (3 * 2.99) * (Kg * scl * μ * W * S * V) ≤
        (9 / 500) ^ 2 * (3 * W * (S ^ 2 - S)) * (scl * Kg) := by
      have h : (0 : ℝ) ≤ (9 / 500) ^ 2 * (3 * W * S) * (scl * Kg) := by positivity
      have hh := mul_le_mul_of_nonneg_right hS1 h
      linarith [hh]
    have hfin : 32 * K * Cn * a ^ 2 * μ * k * W * S * V / (scl * Kg) ≤
        (9 / 500) ^ 2 * (3 * W * (S ^ 2 - S)) := by
      rw [div_le_iff₀ (mul_pos hscl hKg)]
      linarith
    linarith [hkey, hfin]
  linarith

end Work.BoseB1Cube

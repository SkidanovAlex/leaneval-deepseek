import Mathlib

namespace Work.RPB.B1a

theorem nocap_of_sq_bounds (P Q : ℝ → ℝ) {σ M r : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hMr : M * r ≤ 1 / 8) (hσ : σ = 1 ∨ σ = -1)
    (hPb : ∀ x, |x| ≤ 2 * r → |P x| ≤ M * x ^ 2)
    (hQb : ∀ x, |x| ≤ 2 * r → |Q x - σ * x| ≤ M * x ^ 2) :
    ∀ x, |x| ≤ 2 * r → |Q x| < r → P x + Real.sqrt (r ^ 2 - (Q x) ^ 2) ≤ r := by
  intro x hx _
  have hrle : (0:ℝ) ≤ r := le_of_lt hr
  have hM0 : (0:ℝ) ≤ M := hM
  -- `x ^ 2 ≤ (2 * r) ^ 2`
  have hx2 : x ^ 2 ≤ 4 * r ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x, hrle]
  -- `M * x ^ 2 ≤ r / 2`
  have hMx2_le_half : M * x ^ 2 ≤ r / 2 := by
    nlinarith [hx2, hM0, hMr, hr]
  -- `M * x ^ 2 ≤ |x| / 4`
  have hMx2_le_quarter : M * x ^ 2 ≤ |x| / 4 := by
    nlinarith [sq_abs x, abs_nonneg x, hx, hM0, hMr, hr]
  -- `|σ * x| = |x|`
  have hsig_abs : |σ * x| = |x| := by
    rcases hσ with h | h <;> simp [h]
  -- reverse triangle: `|σ * x| - |Q x - σ * x| ≤ |Q x|`
  have hq_low : 3 / 4 * |x| ≤ |Q x| := by
    have h1 : |σ * x| ≤ |Q x| + |Q x - σ * x| := by
      calc |σ * x| = |Q x - (Q x - σ * x)| := by ring_nf
        _ ≤ |Q x| + |Q x - σ * x| := abs_sub _ _
    rw [hsig_abs] at h1
    nlinarith [h1, hQb x hx, hMx2_le_quarter]
  -- `(9 / 16) * x ^ 2 ≤ (Q x) ^ 2`
  have hq2 : 9 / 16 * x ^ 2 ≤ (Q x) ^ 2 := by
    have hsq : (3 / 4 * |x|) ^ 2 ≤ (|Q x|) ^ 2 := by
      nlinarith [hq_low, abs_nonneg x, abs_nonneg (Q x)]
    nlinarith [hsq, sq_abs x, sq_abs (Q x)]
  -- `|P x| ≤ r / 2`
  have hp_bound : |P x| ≤ r / 2 := by
    linarith [hPb x hx, hMx2_le_half]
  have hp_lt_r : P x < r := by
    have := (abs_le.mp hp_bound).2
    linarith
  -- `2 * r * P x - (P x) ^ 2 ≤ (Q x) ^ 2`
  have hpq : 2 * r * P x - (P x) ^ 2 ≤ (Q x) ^ 2 := by
    have h2 : 2 * r * P x - (P x) ^ 2 ≤ 2 * r * |P x| := by
      nlinarith [le_abs_self (P x), sq_nonneg (P x), hr]
    have h3 : 2 * r * |P x| ≤ 2 * r * (M * x ^ 2) := by
      nlinarith [hPb x hx, hr]
    have h4 : 2 * r * (M * x ^ 2) ≤ 9 / 16 * x ^ 2 := by
      nlinarith [hMr, sq_nonneg x, hr, hM0]
    linarith [h2, h3, h4, hq2]
  -- `r ^ 2 - (Q x) ^ 2 ≤ (r - P x) ^ 2`
  have hmain : r ^ 2 - (Q x) ^ 2 ≤ (r - P x) ^ 2 := by
    nlinarith [hpq]
  have hsqrt := (Real.sqrt_le_left (by linarith : (0:ℝ) ≤ r - P x)).2 hmain
  linarith [hsqrt]

end Work.RPB.B1a

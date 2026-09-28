import Mathlib

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux.GmdAux

/-- For `X > 0` and `Y ≥ 0`: `X * (Y / X) ^ θ = X ^ (1 - θ) * Y ^ θ`. -/
private lemma mul_div_rpow_aux {X Y : ℝ} (hX : 0 < X) (hY : 0 ≤ Y) (θ : ℝ) :
    X * (Y / X) ^ θ = X ^ (1 - θ) * Y ^ θ := by
  have h1 : X * (X^θ)⁻¹ = X ^ (1 - θ) := by
    rw [← Real.rpow_neg hX.le θ]
    calc X * X^(-θ) = X^1 * X^(-θ) := by rw [Real.rpow_one]
      _ = X^(1 + -θ) := (Real.rpow_add hX 1 (-θ)).symm
      _ = X^(1 - θ) := by rw [show (1:ℝ) + -θ = 1 - θ by ring]
  calc X * (Y / X) ^ θ = X * (Y^θ / X^θ) := by rw [Real.div_rpow hY hX.le]
    _ = (X * (X^θ)⁻¹) * Y^θ := by ring
    _ = X ^ (1 - θ) * Y^θ := by rw [h1]

/-- Comparison of a real power with a multiplied exponential factor:
if `N / C ≤ a ^ k` with `a > 1`, `θ > 0`, `N > 0`, `C > 0`, then
`N * (a ^ (-θ)) ^ k ≤ C ^ θ * N ^ (1 - θ)`. -/
theorem NMulPowLe {a θ N C : ℝ} (ha : 1 < a) (hθ0 : 0 < θ) (hN : 0 < N) (hC : 0 < C)
    {k : ℕ} (hcross : N / C ≤ a ^ k) :
    N * (a ^ (-θ)) ^ k ≤ C ^ θ * N ^ (1 - θ) := by
  have ha0 : 0 < a := lt_trans one_pos ha
  have hNCpos : 0 < N / C := div_pos hN hC
  -- `N / C ≤ a ^ (k : ℝ)`
  have hcross' : N / C ≤ a ^ (k:ℝ) := by
    rw [Real.rpow_natCast]; exact hcross
  have haKpos : 0 < a ^ (k:ℝ) := Real.rpow_pos_of_pos ha0 _
  -- inverting the hypothesis: `a ^ (-(k : ℝ)) ≤ C / N`
  have h1 : a ^ (-(k:ℝ)) ≤ C / N := by
    have h := (inv_le_inv₀ haKpos hNCpos).mpr hcross'
    have hae : a ^ (-(k:ℝ)) = (a ^ (k:ℝ))⁻¹ := Real.rpow_neg ha0.le (k:ℝ)
    have hde : (N/C)⁻¹ = C/N := by rw [inv_div]
    rw [← hae, hde] at h
    exact h
  -- raise to the power `θ > 0`
  have h2 : (a ^ (-(k:ℝ))) ^ θ ≤ (C/N) ^ θ :=
    Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos ha0 _)) h1 hθ0.le
  -- rewrite `(a ^ (-(k:ℝ))) ^ θ` as `(a ^ (-θ)) ^ k`
  have h3 : (a ^ (-(k:ℝ))) ^ θ = (a ^ (-θ)) ^ k := by
    calc (a ^ (-(k:ℝ))) ^ θ = a ^ ((-(k:ℝ)) * θ) := (Real.rpow_mul ha0.le (-(k:ℝ)) θ).symm
      _ = a ^ ((-θ) * (k:ℝ)) := by ring_nf
      _ = (a ^ (-θ)) ^ (k:ℝ) := Real.rpow_mul ha0.le (-θ) (k:ℝ)
      _ = (a ^ (-θ)) ^ k := by rw [Real.rpow_natCast]
  -- algebra: `N * (C / N) ^ θ = C ^ θ * N ^ (1 - θ)`
  have h4 : N * (C/N)^θ = C^θ * N^(1-θ) := by
    rw [mul_div_rpow_aux hN hC.le θ]
    ring
  calc N * (a ^ (-θ))^k = N * (a ^ (-(k:ℝ)))^θ := by rw [h3]
    _ ≤ N * (C/N)^θ := mul_le_mul_of_nonneg_left h2 hN.le
    _ = C ^ θ * N ^ (1-θ) := h4

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux.GmdAux

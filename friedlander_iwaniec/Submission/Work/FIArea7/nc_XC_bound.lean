import Mathlib
import Submission.Work.FIArea7.NCBasic

namespace Work.FIArea7

/-- Auxiliary: `4 * N + 4 ≤ N^2` for `N ≥ 5`. -/
private lemma four_mul_add_four_le_sq {N : ℝ} (hN5 : 5 ≤ N) : 4 * N + 4 ≤ N ^ 2 := by
  nlinarith [sq_nonneg (N - 5), hN5]

theorem nc_XC_bound {N X θ UB δ₁ : ℝ} {K : ℕ}
    (hN5 : 5 ≤ N) (hX1 : 1 ≤ X) (hX8 : X ^ 8 ≤ N ^ δ₁) (hδ0 : 0 < δ₁) (hδ32 : δ₁ < 3 / 32)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hK1 : 1 ≤ (K : ℝ))
    (hKhi : (K : ℝ) ≤ 2 * X ^ 3 * (Real.log (N + 2)) ^ 20)
    (hUB0 : 0 < UB) (hUBhi : UB ≤ 4 * θ * N + 2) :
    X * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
      ≤ 6 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 + 2 * N ^ (δ₁ / 4) * Real.log N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  -- logarithm facts
  have hL1 : 1 ≤ Real.log (N + 2) := one_le_log_of_three_le (by linarith)
  have hLnn : 0 ≤ Real.log (N + 2) := le_trans (by norm_num) hL1
  have hLge1 : 1 ≤ (Real.log (N + 2)) ^ 20 := one_le_pow₀ hL1
  have hLnn20 : 0 ≤ (Real.log (N + 2)) ^ 20 := pow_nonneg hLnn 20
  -- power bounds for X
  have hXle : X ≤ N ^ (δ₁ / 8) := le_rpow_div_eight_of_pow_eight_le hX0 hN0 hX8
  have hX2 : X ^ 2 ≤ N ^ (δ₁ / 4) := by
    have h := pow_le_rpow_of_le_rpow hX0 hN0 hXle 2
    have he : δ₁ / 8 * ((2 : ℕ) : ℝ) = δ₁ / 4 := by ring
    rwa [he] at h
  have hX5 : X ^ 5 ≤ N ^ (5 * δ₁ / 8) := by
    have h := pow_le_rpow_of_le_rpow hX0 hN0 hXle 5
    have he : δ₁ / 8 * ((5 : ℕ) : ℝ) = 5 * δ₁ / 8 := by ring
    rwa [he] at h
  have hNrdnn : 0 ≤ N ^ (1 - δ₁) := Real.rpow_nonneg hN0.le _
  -- rpow product identities
  have he1 : N ^ (5 * δ₁ / 8) * N ^ (1 - δ₁) = N ^ (1 - 3 * δ₁ / 8) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have he2 : N ^ (δ₁ / 4) * N ^ (1 - δ₁) = N ^ (1 - 3 * δ₁ / 4) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  -- comparison `N^(1-3δ/4) ≤ 2 N^(1-3δ/8) (log(N+2))^20`
  have hB_le : N ^ (1 - 3 * δ₁ / 4) ≤ 2 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 := by
    have hg : -(3 * δ₁ / 8) ≤ 0 := by linarith
    have hneg : N ^ (-(3 * δ₁ / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 hg
    have hsplit : N ^ (1 - 3 * δ₁ / 4) = N ^ (1 - 3 * δ₁ / 8) * N ^ (-(3 * δ₁ / 8)) := by
      rw [show 1 - 3 * δ₁ / 4 = (1 - 3 * δ₁ / 8) + (-(3 * δ₁ / 8)) by ring,
        Real.rpow_add hN0]
    have h2L : 1 ≤ 2 * (Real.log (N + 2)) ^ 20 := by linarith
    rw [hsplit]
    calc N ^ (1 - 3 * δ₁ / 8) * N ^ (-(3 * δ₁ / 8))
        ≤ N ^ (1 - 3 * δ₁ / 8) * 1 :=
          mul_le_mul_of_nonneg_left hneg (Real.rpow_nonneg hN0.le _)
      _ = N ^ (1 - 3 * δ₁ / 8) := by ring
      _ = N ^ (1 - 3 * δ₁ / 8) * 1 := (mul_one _).symm
      _ ≤ N ^ (1 - 3 * δ₁ / 8) * (2 * (Real.log (N + 2)) ^ 20) :=
          mul_le_mul_of_nonneg_left h2L (Real.rpow_nonneg hN0.le _)
      _ = 2 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 := by ring
  -- first summand
  have hA2 : X ^ 2 * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁)
      ≤ X ^ 2 * (4 * X ^ 3 * (Real.log (N + 2)) ^ 20 + 1) * N ^ (1 - δ₁) := by
    have hK2 : 2 * (K : ℝ) + 1 ≤ 4 * X ^ 3 * (Real.log (N + 2)) ^ 20 + 1 := by linarith
    have h1 : (2 * (K : ℝ) + 1) * N ^ (1 - δ₁)
        ≤ (4 * X ^ 3 * (Real.log (N + 2)) ^ 20 + 1) * N ^ (1 - δ₁) :=
          mul_le_mul_of_nonneg_right hK2 hNrdnn
    calc X ^ 2 * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁)
        = X ^ 2 * ((2 * (K : ℝ) + 1) * N ^ (1 - δ₁)) := by ring
      _ ≤ X ^ 2 * ((4 * X ^ 3 * (Real.log (N + 2)) ^ 20 + 1) * N ^ (1 - δ₁)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg X)
      _ = X ^ 2 * (4 * X ^ 3 * (Real.log (N + 2)) ^ 20 + 1) * N ^ (1 - δ₁) := by ring
  have hA3 : 4 * X ^ 5 * (Real.log (N + 2)) ^ 20 * N ^ (1 - δ₁)
      ≤ 4 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 := by
    have hc : 0 ≤ 4 * (Real.log (N + 2)) ^ 20 * N ^ (1 - δ₁) :=
      mul_nonneg (mul_nonneg (by norm_num) hLnn20) hNrdnn
    calc 4 * X ^ 5 * (Real.log (N + 2)) ^ 20 * N ^ (1 - δ₁)
        = X ^ 5 * (4 * (Real.log (N + 2)) ^ 20 * N ^ (1 - δ₁)) := by ring
      _ ≤ N ^ (5 * δ₁ / 8) * (4 * (Real.log (N + 2)) ^ 20 * N ^ (1 - δ₁)) :=
          mul_le_mul_of_nonneg_right hX5 hc
      _ = 4 * (Real.log (N + 2)) ^ 20 * (N ^ (5 * δ₁ / 8) * N ^ (1 - δ₁)) := by ring
      _ = 4 * (Real.log (N + 2)) ^ 20 * N ^ (1 - 3 * δ₁ / 8) := by rw [he1]
      _ = 4 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 := by ring
  have hA4 : X ^ 2 * N ^ (1 - δ₁) ≤ 2 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 := by
    calc X ^ 2 * N ^ (1 - δ₁) ≤ N ^ (δ₁ / 4) * N ^ (1 - δ₁) :=
          mul_le_mul_of_nonneg_right hX2 hNrdnn
      _ = N ^ (1 - 3 * δ₁ / 4) := he2
      _ ≤ 2 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 := hB_le
  have hA : X * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁))
      ≤ 6 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 := by
    calc X * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁))
        = X ^ 2 * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) := by ring
      _ ≤ X ^ 2 * (4 * X ^ 3 * (Real.log (N + 2)) ^ 20 + 1) * N ^ (1 - δ₁) := hA2
      _ = 4 * X ^ 5 * (Real.log (N + 2)) ^ 20 * N ^ (1 - δ₁) + X ^ 2 * N ^ (1 - δ₁) := by ring
      _ ≤ 4 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20
            + 2 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 := add_le_add hA3 hA4
      _ = 6 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 := by ring
  -- the logarithm of `UB + 2`
  have hUB2 : Real.log (UB + 2) ≤ 2 * Real.log N := by
    have hθN : θ * N ≤ N := by
      have h := mul_le_mul_of_nonneg_right hθ1 hN0.le
      simpa using h
    have hUB4 : UB ≤ 4 * N + 2 := by nlinarith [hUBhi, hθN]
    have hle : UB + 2 ≤ N ^ 2 := by
      have := four_mul_add_four_le_sq hN5
      linarith
    have h1 : Real.log (UB + 2) ≤ Real.log (N ^ 2) := Real.log_le_log (by linarith) hle
    simpa [Real.log_pow] using h1
  -- second summand
  have hB : X * (X * Real.log (UB + 2)) ≤ 2 * N ^ (δ₁ / 4) * Real.log N := by
    have hlog0 : 0 ≤ Real.log (UB + 2) := Real.log_nonneg (by linarith)
    calc X * (X * Real.log (UB + 2)) = X ^ 2 * Real.log (UB + 2) := by ring
      _ ≤ N ^ (δ₁ / 4) * Real.log (UB + 2) := mul_le_mul_of_nonneg_right hX2 hlog0
      _ ≤ N ^ (δ₁ / 4) * (2 * Real.log N) :=
          mul_le_mul_of_nonneg_left hUB2 (Real.rpow_nonneg hN0.le _)
      _ = 2 * N ^ (δ₁ / 4) * Real.log N := by ring
  calc X * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁) + X * Real.log (UB + 2))
      = X * (X * (2 * (K : ℝ) + 1) * N ^ (1 - δ₁)) + X * (X * Real.log (UB + 2)) := by ring
    _ ≤ 6 * N ^ (1 - 3 * δ₁ / 8) * (Real.log (N + 2)) ^ 20 + 2 * N ^ (δ₁ / 4) * Real.log N :=
        add_le_add hA hB

end Work.FIArea7

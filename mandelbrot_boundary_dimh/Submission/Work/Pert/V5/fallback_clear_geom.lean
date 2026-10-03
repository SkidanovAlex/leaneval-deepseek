import Mathlib

namespace Work.Pert.V5

theorem fallback_clear_geom {Ξ M X ℓ : ℝ}
    (hM : 2 ^ 10 ≤ M) (hΞ : 0 < Ξ)
    (hℓ : ℓ ≤ 14 * (M + Ξ))
    (hΞM : Ξ ≤ M + 2 * X)
    (hfail1 : 2 ^ 37 * X < 1025 * ℓ)
    (hfail2 : 2 ^ 24 * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) < 1025 * ℓ) :
    ∀ ξ : ℝ, -(Ξ + 2 ^ 10 + 2 * M) ≤ ξ → ξ ≤ -M + X →
      2 ^ 10 ≤ |ξ| ∧ |ξ| ≤ 20 * (M + 2 + Ξ) := by
  intro ξ hξ1 hξ2
  have hM1024 : (1024 : ℝ) ≤ M := by
    have h := hM
    norm_num at h
    exact h
  -- ## Step 1: the logarithmic factor is at least 1, since 2 + 16*(M+2+Ξ) ≥ 16418 > 3 = exp 1.
  have hlog : (1 : ℝ) ≤ Real.log (2 + 16 * (M + 2 + Ξ)) := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
      rwa [Real.log_exp] at h
    have harg : (3 : ℝ) ≤ 2 + 16 * (M + 2 + Ξ) := by nlinarith
    exact le_trans h3 (Real.log_le_log (by norm_num) harg)
  have h2log : (2 : ℝ) ≤ 1 + Real.log (2 + 16 * (M + 2 + Ξ)) := by linarith
  -- ## Step 2: 2^25 < 1025 ℓ ≤ 14350 (M+Ξ), hence 2338 < M+Ξ.
  have h25 : (2 : ℝ) ^ 25 < 1025 * ℓ := by
    calc (2 : ℝ) ^ 25 = 2 ^ 24 * 2 := by norm_num
      _ ≤ 2 ^ 24 * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) :=
            mul_le_mul_of_nonneg_left h2log (by norm_num)
      _ < 1025 * ℓ := hfail2
  have h14350 : 1025 * ℓ ≤ 14350 * (M + Ξ) := by nlinarith [hℓ]
  have hs2338 : (2338 : ℝ) < M + Ξ := by
    have hnum : (14350 : ℝ) * 2338 < 2 ^ 25 := by norm_num
    linarith
  -- ## Step 3: 2^37 X < 14350 (M+Ξ).
  have hX1 : (2 : ℝ) ^ 37 * X < 14350 * (M + Ξ) := by linarith
  -- ## Step 4: Ξ ≤ M + 2X gives M + Ξ ≤ 2M + 2X.
  have hsle : M + Ξ ≤ 2 * M + 2 * X := by linarith
  have hD : (0 : ℝ) < 2 ^ 37 - 28700 := by norm_num
  -- ## Step 5: M is large: 1168 < M.
  have hMlo : (1168 : ℝ) < M := by
    have h2X : (2 : ℝ) ^ 37 * (2 * X) < 28700 * (M + Ξ) := by linarith
    have hstep : (2 : ℝ) ^ 37 * (2 * M) > (2 ^ 37 - 28700) * (M + Ξ) := by linarith
    have h5 : (2 : ℝ) ^ 37 * (2 * M) > (2 ^ 37 - 28700) * 2338 := by
      have := mul_lt_mul_of_pos_left hs2338 hD
      linarith
    have hnum : (2 : ℝ) ^ 37 * 2337 < (2 ^ 37 - 28700) * 2338 := by norm_num
    have h6 : (2 : ℝ) ^ 37 * (2 * M) > (2 : ℝ) ^ 37 * 2337 := by linarith
    nlinarith [h6]
  -- ## Step 6: X is small: 10^7 * X < 3M, hence X < M - 1024.
  have hX3 : (2 ^ 37 - 28700) * X < 28700 * M := by
    have h1 : (2 : ℝ) ^ 37 * X < 14350 * (2 * M + 2 * X) := by
      have h := mul_le_mul_of_nonneg_left hsle (by norm_num : (0 : ℝ) ≤ 14350)
      linarith
    linarith
  have hX4 : (10 : ℝ) ^ 7 * X < 3 * M := by
    have hnum : (28700 : ℝ) * 10 ^ 7 ≤ 3 * (2 ^ 37 - 28700) := by norm_num
    have hMpos : (0 : ℝ) < M := by linarith
    have hkey : 28700 * 10 ^ 7 * M ≤ 3 * (2 ^ 37 - 28700) * M := by nlinarith
    have h1 : (10 : ℝ) ^ 7 * ((2 : ℝ) ^ 37 - 28700) * X
        < (10 : ℝ) ^ 7 * (28700 * M) := by nlinarith [hX3]
    nlinarith [h1, hkey, hD]
  have hX5 : X ≤ M - 1024 := by
    have hnum : 3 * M < (10 : ℝ) ^ 7 * (M - 1024) := by nlinarith
    linarith
  -- ## Step 7: ξ < 0 and the two bounds.
  have hξneg : ξ < 0 := by linarith
  have hξle : ξ ≤ -1024 := by linarith
  constructor
  · rw [abs_of_neg hξneg]
    linarith
  · rw [abs_of_neg hξneg]
    have h1 : -ξ ≤ Ξ + 2 ^ 10 + 2 * M := by linarith
    have h2 : Ξ + 2 ^ 10 + 2 * M ≤ 20 * (M + 2 + Ξ) := by
      have h1024 : (2 : ℝ) ^ 10 = 1024 := by norm_num
      nlinarith
    linarith

end Work.Pert.V5

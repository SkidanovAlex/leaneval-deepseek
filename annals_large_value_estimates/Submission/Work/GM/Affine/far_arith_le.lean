import Mathlib

set_option linter.unusedVariables false

namespace Work.GM.Affine

/-- Arithmetic reduction from GM §9: from `X₀^M * M = 2 a² 4^M` and `X₀ ≤ X₁`,
together with the exponent hypothesis `7 + 2δ ≤ M·2δ` and `T ≥ 1`, the "far" term
`2 (a T^{3+δ} V)² T^{M+1} / (M (T^{1+2δ} X₁/4)^M)` is at most `V²`. -/
theorem far_arith_le {T V a X₀ X₁ δ : ℝ} {M : ℕ} (hT1 : 1 ≤ T) (hV : 0 ≤ V)
    (hM2 : 2 ≤ M) (hδ : 0 < δ) (hMδ : 7 + 2 * δ ≤ (M : ℝ) * (2 * δ))
    (hX₀pos : 0 < X₀) (hX₁ : X₀ ≤ X₁)
    (hX₀ : X₀ ^ M * (M : ℝ) = 2 * a ^ 2 * 4 ^ M) :
    2 * (a * (T ^ 3 * T ^ δ) * V) ^ 2 * T ^ (M + 1)
        / ((M : ℝ) * (T ^ (1 + 2 * δ) * X₁ / 4) ^ M) ≤ V ^ 2 := by
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hT0le : (0:ℝ) ≤ T := hT0.le
  have hMpos_nat : 0 < M := by omega
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos_nat
  have hX₁pos : (0:ℝ) < X₁ := lt_of_lt_of_le hX₀pos hX₁
  have hX0div : (0:ℝ) ≤ X₀/4 := by linarith [hX₀pos]
  have hX1div : (0:ℝ) < X₁/4 := by linarith [hX₁pos]
  have h4ne : ((4:ℝ)^M) ≠ 0 := by positivity
  -- Main algebraic identity: `2 a² = M (X₀/4)^M`.
  have h2a2 : 2 * a^2 = (M:ℝ) * (X₀/4)^M := by
    have h : 2 * a^2 = X₀^M * (M:ℝ) / 4^M := by
      rw [eq_div_iff h4ne]
      rw [hX₀]
    rw [h]
    rw [div_pow]
    ring
  have hXpow : (X₀/4)^M ≤ (X₁/4)^M :=
    pow_le_pow_left₀ hX0div (by linarith) M
  -- `(T^3 T^δ)^2 = T^{6+2δ}`
  have hsq : (T^3 * T^δ)^2 = T^(6 + 2*δ) := by
    rw [mul_pow]
    rw [show (T^3:ℝ)^2 = T^(6:ℝ) from by
        rw [show (T^3:ℝ) = T^(3:ℝ) from (Real.rpow_natCast T 3).symm,
            ← Real.rpow_natCast, ← Real.rpow_mul hT0le]
        norm_num]
    rw [show (T^δ:ℝ)^2 = T^(2*δ) from by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0le]
        ring_nf]
    rw [← Real.rpow_add hT0]
  have hL : (T^3 * T^δ)^2 * T^(M+1) = T^((6 + 2*δ) + ((M:ℝ)+1)) := by
    rw [hsq]
    rw [show T^(M+1) = T^((M:ℝ)+1) from by
        rw [← Real.rpow_natCast]; push_cast; ring]
    rw [← Real.rpow_add hT0]
  have hR : (T^(1+2*δ))^M = T^((1+2*δ)*((M:ℝ))) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hT0le]
  have hexp_le : (6 + 2*δ) + ((M:ℝ)+1) ≤ (1+2*δ) * (M:ℝ) := by
    nlinarith [hMδ]
  -- The `T`-part of the estimate, by monotonicity of `T ^ ·` for `T ≥ 1`.
  have hTpow : (T^3 * T^δ)^2 * T^(M+1) ≤ (T^(1+2*δ))^M := by
    rw [hL, hR]
    exact Real.rpow_le_rpow_of_exponent_le hT1 hexp_le
  have hcore : (X₀/4)^M * ((T^3 * T^δ)^2 * T^(M+1)) ≤ (X₁/4)^M * (T^(1+2*δ))^M :=
    mul_le_mul hXpow hTpow (mul_nonneg (sq_nonneg _) (pow_nonneg hT0le _))
      (pow_nonneg hX1div.le M)
  have hmulpow : (T^(1+2*δ) * X₁/4)^M = (T^(1+2*δ))^M * (X₁/4)^M := by
    rw [show T^(1+2*δ) * X₁/4 = T^(1+2*δ) * (X₁/4) from by ring]
    exact mul_pow _ _ _
  have hmain : 2 * (a * (T^3 * T^δ) * V)^2 * T^(M+1)
      ≤ ((M:ℝ) * (T^(1+2*δ) * X₁/4)^M) * V^2 := by
    calc 2 * (a * (T^3 * T^δ) * V)^2 * T^(M+1)
        = (2 * a^2) * ((T^3 * T^δ)^2 * T^(M+1)) * V^2 := by ring
      _ = (M:ℝ) * ((X₀/4)^M * ((T^3 * T^δ)^2 * T^(M+1))) * V^2 := by
            rw [h2a2]
            ring
      _ ≤ (M:ℝ) * ((X₁/4)^M * (T^(1+2*δ))^M) * V^2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcore hMpos.le) (sq_nonneg V)
      _ = ((M:ℝ) * (T^(1+2*δ) * X₁/4)^M) * V^2 := by
            rw [hmulpow]
            ring
  have hbase : (0:ℝ) < T^(1+2*δ) * X₁ / 4 := by
    apply div_pos _ (by norm_num)
    exact mul_pos (Real.rpow_pos_of_pos hT0 _) hX₁pos
  have hDpos : (0:ℝ) < (M:ℝ) * (T^(1+2*δ) * X₁/4)^M :=
    mul_pos hMpos (pow_pos hbase M)
  rw [div_le_iff₀ hDpos]
  calc 2 * (a * (T^3 * T^δ) * V)^2 * T^(M+1)
      ≤ ((M:ℝ) * (T^(1+2*δ) * X₁/4)^M) * V^2 := hmain
    _ = V^2 * ((M:ℝ) * (T^(1+2*δ) * X₁/4)^M) := by ring

end Work.GM.Affine

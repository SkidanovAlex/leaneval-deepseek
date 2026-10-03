import Mathlib

namespace Work.Peluse.SwapA

/-- The ratio `M'/(M' + (t+1)M₂)` of the endgame is bounded below by a power of `γ`, given that
`M' ≥ C_R (γ/4)^{K_R} M₁` and `M₂ ≤ M₁`. -/
theorem M_ratio_lower (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {C_R M₁ M₂ M' : ℝ} {K_R t : ℕ}
    (hC_R0 : 0 < C_R) (hC_R1 : C_R ≤ 1) (hM₂1 : 1 ≤ M₂) (hM₂M₁ : M₂ ≤ M₁)
    (hM'le : M' ≤ M₁) (hM'ge : C_R * (γ / 4) ^ K_R * M₁ ≤ M') :
    C_R * ((1 : ℝ) / 4) ^ K_R / ((t : ℝ) + 2) * γ ^ K_R ≤ M' / (M' + ((t : ℝ) + 1) * M₂) := by
  -- Rewrite `(γ/4)^K_R` so that the whole statement uses only `γ^K_R` and `(1/4)^K_R`.
  have hpow : (γ / 4) ^ K_R = γ ^ K_R * ((1 : ℝ) / 4) ^ K_R := by
    rw [show γ / 4 = γ * (1 / 4) by ring, mul_pow]
  have hM1 : 0 < M₁ := by linarith
  have hM20 : 0 < M₂ := by linarith
  have ht2 : (0 : ℝ) < (t : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  have hgp0 : 0 < γ ^ K_R := pow_pos hγ0 K_R
  have h4p0 : 0 < ((1 : ℝ) / 4) ^ K_R := pow_pos (by norm_num) K_R
  -- `M' > 0` follows from the lower bound on `M'`.
  have hM'0 : 0 < M' :=
    lt_of_lt_of_le (mul_pos (mul_pos hC_R0 (pow_pos (by linarith) K_R)) hM1) hM'ge
  have hfac : (0 : ℝ) ≤ C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R :=
    le_of_lt (mul_pos (mul_pos hC_R0 h4p0) hgp0)
  have hD0 : 0 < M' + ((t : ℝ) + 1) * M₂ := by
    have h1 : 0 < ((t : ℝ) + 1) * M₂ := by
      have : (0 : ℝ) < (t : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
        linarith
      exact mul_pos this hM20
    linarith
  -- The lower bound on `M'` in the form used below.
  have hstep1 : C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R * M₁ ≤ M' := by
    have h := hM'ge
    rw [hpow] at h
    nlinarith [h]
  -- The denominator `M' + (t+1)M₂` is at most `M₁ (t+2)`.
  have hDle : M' + ((t : ℝ) + 1) * M₂ ≤ M₁ * ((t : ℝ) + 2) := by
    have h1 : ((t : ℝ) + 1) * M₂ ≤ ((t : ℝ) + 1) * M₁ := by
      apply mul_le_mul_of_nonneg_left hM₂M₁
      have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
      linarith
    nlinarith [hM'le, h1]
  have hdiv : (M' + ((t : ℝ) + 1) * M₂) / ((t : ℝ) + 2) ≤ M₁ := by
    rw [div_le_iff₀ ht2]
    linarith
  rw [le_div_iff₀ hD0]
  calc (C_R * ((1 : ℝ) / 4) ^ K_R / ((t : ℝ) + 2) * γ ^ K_R) * (M' + ((t : ℝ) + 1) * M₂)
      = C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R * ((M' + ((t : ℝ) + 1) * M₂) / ((t : ℝ) + 2)) := by
        ring
    _ ≤ C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R * M₁ := mul_le_mul_of_nonneg_left hdiv hfac
    _ ≤ M' := hstep1

end Work.Peluse.SwapA

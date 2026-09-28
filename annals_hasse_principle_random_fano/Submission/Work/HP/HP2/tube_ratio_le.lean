import Mathlib

set_option linter.unusedVariables false

namespace Work.HP.HP2

/-- Arithmetic core of the tube-radius comparison: if `W > 0`, `κ ≥ 1`, `κ ≥ 8(n+1)`, `L ≥ 1`,
`m ≥ 1` and `W * L^m * κ ≤ T`, then the `8(n+1)W`-tube radius `ρ := 8(n+1)W` satisfies
`ρ/T ≤ L^{-m}` and `(ρ/T)^{1/Ksub} ≤ L^{-m/Ksub}` (for `Ksub > 0`). -/
lemma tube_ratio_le {n m : ℕ} {κ Ksub W L T : ℝ}
    (hKsub : 0 < Ksub) (hW : 0 < W) (hκ : 1 ≤ κ) (hκ8 : 8 * ((n : ℝ) + 1) ≤ κ)
    (hL : 1 ≤ L) (hm : 1 ≤ m) (hT : W * L ^ m * κ ≤ T) :
    (8 * ((n : ℝ) + 1) * W) / T ≤ L ^ (-(m : ℝ)) ∧
    ((8 * ((n : ℝ) + 1) * W) / T) ^ (1 / Ksub) ≤ L ^ (-((m : ℝ) / Ksub)) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hLmpos : 0 < L ^ m := pow_pos hLpos m
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  -- Core estimate: `8(n+1)W * L^m ≤ T`, obtained from `8(n+1) ≤ κ` and `W L^m κ ≤ T`.
  have hkey : 8 * ((n : ℝ) + 1) * W * L ^ m ≤ T := by
    have h1 : 8 * ((n : ℝ) + 1) * (W * L ^ m) ≤ κ * (W * L ^ m) :=
      mul_le_mul_of_nonneg_right hκ8 (by positivity)
    calc 8 * ((n : ℝ) + 1) * W * L ^ m = 8 * ((n : ℝ) + 1) * (W * L ^ m) := by ring
      _ ≤ κ * (W * L ^ m) := h1
      _ = W * L ^ m * κ := by ring
      _ ≤ T := hT
  -- Multiplying by `(L^m)⁻¹ ≥ 0` gives `8(n+1)W ≤ L^{-m} T`.
  have hmain : 8 * ((n : ℝ) + 1) * W ≤ L ^ (-(m : ℝ)) * T := by
    have hρ : 8 * ((n : ℝ) + 1) * W ≤ T / L ^ m := (le_div_iff₀ hLmpos).mpr hkey
    rw [div_eq_mul_inv] at hρ
    rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
    linarith [hρ]
  have hfirst : (8 * ((n : ℝ) + 1) * W) / T ≤ L ^ (-(m : ℝ)) := by
    rw [div_le_iff₀ hTpos]
    linarith [hmain]
  refine ⟨hfirst, ?_⟩
  -- Raise the first inequality to the power `1/Ksub > 0`, using monotonicity of `rpow`.
  have ha : (0 : ℝ) ≤ (8 * ((n : ℝ) + 1) * W) / T := by positivity
  have hstep := Real.rpow_le_rpow ha hfirst (by positivity : (0 : ℝ) ≤ 1 / Ksub)
  have hexp : (-(m : ℝ)) * (1 / Ksub) = -((m : ℝ) / Ksub) := by ring
  rw [← Real.rpow_mul hLpos.le, hexp] at hstep
  exact hstep

end Work.HP.HP2

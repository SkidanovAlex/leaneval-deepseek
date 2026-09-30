import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BMF.SD

/-- Arithmetic bound: if `C = 2π·4^{k+1}·C₀/(2δ) + 1`, `d > C(C₂+1)/L` and
`‖ζ-1‖ ≥ 4d`, then `q·(1 + L·(2π·4^{k+1}·C₂/L))·(2/‖ζ-1‖) < δ·L`.

The proof isolates `A := 2π·4^{k+1}`, uses `L·(2π·(4^{k+1}C₂/L)) = A·C₂`,
bounds `1 + A·C₂ ≤ A(C₂+1)`, and `2/‖ζ-1‖ < L/(2C(C₂+1))`, reducing the
claim to `C₀·A/(2C) < δ`, which follows from `C > A·C₀/(2δ)`. -/
theorem a_one_bound_final_arith (k : ℕ) (δ C₀ C C₂ L q d : ℝ) (ζ : ℂ)
    (hδ : 0 < δ) (hC₀ : 1 ≤ C₀) (hC₂ : 0 ≤ C₂) (hL : 0 < L) (hq : 0 ≤ q) (hqC₀ : q ≤ C₀)
    (hC : C = 2 * Real.pi * (4:ℝ)^(k+1) * C₀ / (2*δ) + 1)
    (hd : C * (C₂ + 1) / L < d) (hζ : 4 * d ≤ ‖ζ - 1‖) :
    q * ((1 + L * (2 * Real.pi * ((4:ℝ)^(k+1) * C₂ / L))) * (2 / ‖ζ - 1‖)) < δ * L := by
  set A : ℝ := 2 * Real.pi * (4:ℝ)^(k+1) with hAdef
  have hpi_ge : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hpow : (1:ℝ) ≤ (4:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hAge1 : 1 ≤ A := by
    rw [hAdef]
    calc (1:ℝ) ≤ 2 * Real.pi := hpi_ge
      _ = 2 * Real.pi * 1 := by ring
      _ ≤ 2 * Real.pi * (4:ℝ)^(k+1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have hC₂p1 : 0 < C₂ + 1 := by linarith
  have hCpos : 0 < C := by rw [hC]; positivity
  have hdC : 0 < C * (C₂ + 1) / L := div_pos (mul_pos hCpos hC₂p1) hL
  have hdpos : 0 < d := lt_trans hdC hd
  have hmpos : 0 < ‖ζ - 1‖ := lt_of_lt_of_le (by linarith : (0:ℝ) < 4 * d) hζ
  -- Simplify the factor `L * (2π * (4^{k+1} C₂ / L)) = A * C₂`.
  have hLmul : L * (2 * Real.pi * ((4:ℝ)^(k+1) * C₂ / L)) = A * C₂ := by
    rw [hAdef]; field_simp
  rw [hLmul]
  -- Bound `2 / ‖ζ - 1‖ < L / (2 C (C₂ + 1))`.
  have hY : 2 / ‖ζ - 1‖ < L / (2 * C * (C₂ + 1)) := by
    have hstep1 : 2 / ‖ζ - 1‖ ≤ 2 / (4 * d) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith : (0:ℝ) < 4*d) hζ
    have hstep1b : 2 / (4 * d) < L / (2 * C * (C₂ + 1)) := by
      rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < 4*d)
            (mul_pos (by linarith : (0:ℝ) < 2*C) hC₂p1)]
      have htarget : C * (C₂ + 1) < d * L := (div_lt_iff₀ hL).mp hd
      nlinarith
    exact lt_of_le_of_lt hstep1 hstep1b
  have hY0 : 0 ≤ 2 / ‖ζ - 1‖ := div_nonneg (by norm_num) (le_of_lt hmpos)
  -- Bound `1 + A C₂ ≤ A (C₂ + 1)` and `q ≤ C₀`.
  have hAineq : 1 + A * C₂ ≤ A * (C₂ + 1) := by nlinarith [hAge1, hC₂]
  have hAC2 : 0 ≤ A * C₂ := mul_nonneg (le_of_lt hApos) hC₂
  have h1AC2 : 0 ≤ 1 + A * C₂ := by linarith
  have hbound1 : q * (1 + A * C₂) ≤ C₀ * (A * (C₂ + 1)) :=
    mul_le_mul hqC₀ hAineq h1AC2 (le_trans zero_le_one hC₀)
  have hposC0A : 0 < C₀ * (A * (C₂ + 1)) :=
    mul_pos (lt_of_lt_of_le zero_lt_one hC₀) (mul_pos hApos hC₂p1)
  have hbound2 : C₀ * (A * (C₂ + 1)) * (2 / ‖ζ - 1‖)
      < C₀ * (A * (C₂ + 1)) * (L / (2 * C * (C₂ + 1))) :=
    mul_lt_mul_of_pos_left hY hposC0A
  have hchain : q * ((1 + A * C₂) * (2 / ‖ζ - 1‖))
      < C₀ * (A * (C₂ + 1)) * (L / (2 * C * (C₂ + 1))) := by
    have h1 : q * ((1 + A * C₂) * (2 / ‖ζ - 1‖)) = q * (1 + A * C₂) * (2 / ‖ζ - 1‖) := by ring
    rw [h1]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbound1 hY0) hbound2
  have hsimp : C₀ * (A * (C₂ + 1)) * (L / (2 * C * (C₂ + 1))) = C₀ * A * L / (2 * C) := by
    field_simp
  -- Final coefficient bound `C₀ A L / (2C) < δ L`.
  have hfinal : C₀ * A * L / (2 * C) < δ * L := by
    have hkey : C₀ * A / (2 * C) < δ := by
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < 2 * C)]
      have hCA : A * C₀ / (2 * δ) < C := by
        rw [hAdef, hC]; linarith
      have hCA2 : A * C₀ < C * (2 * δ) := (div_lt_iff₀ (by linarith : (0:ℝ) < 2*δ)).mp hCA
      linarith
    have heq : C₀ * A * L / (2 * C) = (C₀ * A / (2 * C)) * L := by ring
    rw [heq]
    exact mul_lt_mul_of_pos_right hkey hL
  exact lt_trans (hchain.trans_eq hsimp) hfinal

end Work.BMF.SD

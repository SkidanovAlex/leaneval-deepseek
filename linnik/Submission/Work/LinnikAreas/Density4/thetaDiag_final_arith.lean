import Mathlib

namespace Work.LinnikAreas.Density4

/-- Numeric/transcendental bound: for every `ε > 0`, `1 - exp(-ε) ≤ 0.34 * (1 + ε)`.

For `ε ≤ 2` this follows from the tangent (convexity) lower bound `exp(-ε) ≥ exp(-1) * (2 - ε)`
together with `exp(-1) ≥ 0.34`; for `ε ≥ 2` it is immediate from `1 - exp(-ε) < 1 ≤ 0.34 * 3`. -/
lemma one_sub_exp_neg_le (ε : ℝ) (_hε : 0 < ε) :
    1 - Real.exp (-ε) ≤ 0.34 * (1 + ε) := by
  have h_exp1 : (0.34 : ℝ) ≤ Real.exp (-1) := by
    have := Real.exp_neg_one_gt_d9
    linarith
  by_cases h2 : ε ≤ 2
  · -- tangent-line bound `exp(-ε) ≥ exp(-1) * (2 - ε)`
    have h1 : (2 - ε) ≤ Real.exp (1 - ε) := by
      have := Real.add_one_le_exp (1 - ε)
      linarith
    have h2n : (0 : ℝ) ≤ 2 - ε := by linarith
    have hmul : 0.34 * (2 - ε) ≤ Real.exp (-1) * (2 - ε) :=
      mul_le_mul_of_nonneg_right h_exp1 h2n
    have hmul2 : Real.exp (-1) * (2 - ε) ≤ Real.exp (-1) * Real.exp (1 - ε) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-1)).le
    have hexp : Real.exp (-1) * Real.exp (1 - ε) = Real.exp (-ε) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [hmul, hmul2, hexp]
  · -- `ε ≥ 2`: crude bound `1 - exp(-ε) < 1 ≤ 0.34 * 3 ≤ 0.34 * (1 + ε)`
    have h2' : 2 ≤ ε := by linarith
    have hexppos : 0 < Real.exp (-ε) := Real.exp_pos _
    nlinarith [h2', hexppos]

theorem thetaDiag_final_arith (ε C₁ C₂ M L κ Q k₁ : ℝ)
    (hε : 0 < ε) (hM : 0 < M) (hL : 0 < L) (hκ : 1 ≤ κ) (hQ : 0 ≤ Q)
    (hC1 : C₁ ≤ 1) (hC1pos : 0 ≤ C₁)
    (hk1 : k₁ ≤ 1 - Real.exp (-ε))
    (hQbig : 15000 ≤ M → 0.34 * M ^ 2 ≤ Q)
    (hC2 : (1 + ε) + C₁ + 10^9 ≤ C₂) :
    k₁ + (1 + ε) * (M * κ - Q + 1) / M ^ 2 + C₁ * κ / M ^ 2 + C₁ / M ^ 2
      ≤ (1 + ε) * κ / M + C₂ * κ / M ^ 2 + C₂ / L := by
  -- `k₁ ≤ 0.34 * (1 + ε)`: the only transcendental input.
  have hk' : k₁ ≤ 0.34 * (1 + ε) :=
    le_trans hk1 (one_sub_exp_neg_le ε hε)
  have hC2pos : 0 < C₂ := by linarith [hε, hC1pos, hC2]
  have hM2 : (0 : ℝ) < M ^ 2 := by positivity
  have hC2C1 : 0 ≤ C₂ - C₁ := by linarith [hC2, hε, hC1pos]
  have hkC : C₂ - C₁ ≤ (C₂ - C₁) * κ := by
    have := mul_le_mul_of_nonneg_left hκ hC2C1
    simpa using this
  -- The crux, after clearing the denominator `M ^ 2`.
  have hkey : k₁ * M ^ 2 ≤ (1 + ε) * (Q - 1) + (C₂ - C₁) * κ - C₁ := by
    by_cases hMbig : 15000 ≤ M
    · -- Large `M`: use `Q ≥ 0.34 M ^ 2`.
      have hQ : 0.34 * M ^ 2 ≤ Q := hQbig hMbig
      have hkM : k₁ * M ^ 2 ≤ 0.34 * (1 + ε) * M ^ 2 :=
        mul_le_mul_of_nonneg_right hk' (sq_nonneg M)
      have hQ1 : (1 + ε) * (0.34 * M ^ 2) ≤ (1 + ε) * Q :=
        mul_le_mul_of_nonneg_left hQ (by linarith)
      nlinarith [hkM, hQ1, hkC, hC1pos, hC1, hC2, hε]
    · -- Small `M`: use `Q ≥ 0` and `M ^ 2 < 15000 ^ 2`, absorbed by the huge `10 ^ 9`.
      have hMlt : M < 15000 := by linarith
      have hk1lt : k₁ < 1 := lt_of_le_of_lt hk1 (by have := Real.exp_pos (-ε); linarith)
      have hkM : k₁ * M ^ 2 ≤ M ^ 2 := by
        have h1 : k₁ ≤ 1 := le_of_lt hk1lt
        nlinarith [sq_nonneg M]
      have hM2lt : M ^ 2 < 225000000 := by nlinarith [hM, hMlt]
      have hQ1 : -(1 + ε) ≤ (1 + ε) * (Q - 1) := by nlinarith [hQ, hε]
      nlinarith [hkM, hM2lt, hQ1, hkC, hC1pos, hC1, hC2, hε]
  have hnum : k₁ * M ^ 2 + (1 + ε) * (M * κ - Q + 1) + C₁ * κ + C₁
      ≤ (1 + ε) * κ * M + C₂ * κ := by
    nlinarith [hkey]
  calc
    k₁ + (1 + ε) * (M * κ - Q + 1) / M ^ 2 + C₁ * κ / M ^ 2 + C₁ / M ^ 2
        = (k₁ * M ^ 2 + (1 + ε) * (M * κ - Q + 1) + C₁ * κ + C₁) / M ^ 2 := by
          field_simp
    _ ≤ ((1 + ε) * κ * M + C₂ * κ) / M ^ 2 := div_le_div_of_nonneg_right hnum hM2.le
    _ = (1 + ε) * κ / M + C₂ * κ / M ^ 2 := by
          field_simp
    _ ≤ (1 + ε) * κ / M + C₂ * κ / M ^ 2 + C₂ / L := by
          have hC2L : 0 ≤ C₂ / L := div_nonneg hC2pos.le hL.le
          linarith

end Work.LinnikAreas.Density4

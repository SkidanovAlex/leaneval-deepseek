import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_final_arith

/-!
# Arithmetic closure of the diagonal estimate (`thetaDiag_final_arith2`)

This is the "second arithmetic form" of the final step of the diagonal
(§11–§12) estimate: an elementary but slightly delicate real-arithmetic
inequality in the style of `thetaDiag_final_arith`, but with the extra
positive term `2 * C₁ * κ / M ^ 2` on the left and with the hypothesis on the
size of `Q` phrased through the auxiliary quantities `Q₀`, `s`:

* `Q₀ - s ≤ Q`, `Q₀ ≥ 0`, `s ≤ 1000 * κ`;
* `15000 ≤ M → 0.34 * M ^ 2 ≤ Q₀`.

The two regimes are:

* `M ≥ 15000`: then `Q ≥ Q₀ - s ≥ 0.34 M ^ 2 - 1000 κ`, so that (using the
  transcendental bound `k₁ ≤ 1 - e^{-ε} ≤ 0.34 (1 + ε)`, proved in
  `thetaDiag_final_arith`) the terms `k₁` and `-(1+ε) Q / M ^ 2` cancel against
  `-0.34 (1+ε)` up to `1000 (1+ε) κ / M ^ 2`;
* `M < 15000`: then `Q ≥ -1000 κ` and `M ^ 2 < 15000 ^ 2`, both absorbed by the
  enormous constant `10 ^ 9` sitting in the hypothesis on `C₂`.

In both cases the remaining term `(1001 (1+ε) + 2 C₁) κ / M ^ 2` is dominated by
`C₂ κ / M ^ 2`, and `C₂ / L ≥ 0` is added at the end.
-/

namespace Work.LinnikAreas.Density4

theorem thetaDiag_final_arith2 (ε C₁ C₂ M L κ Q Q₀ s k₁ : ℝ)
    (hε : 0 < ε) (hM : 0 < M) (hL : 0 < L) (hκ : 1 ≤ κ)
    (hQ : Q₀ - s ≤ Q) (hQ0 : 0 ≤ Q₀) (hs : s ≤ 1000 * κ)
    (hQ0big : 15000 ≤ M → 0.34 * M ^ 2 ≤ Q₀)
    (hk1 : k₁ ≤ 1 - Real.exp (-ε))
    (hC1 : C₁ ≤ 1) (hC1pos : 0 ≤ C₁)
    (hC2 : (1 + ε) + C₁ + 10^9 + 2000 * (1 + ε) ≤ C₂) :
    k₁ + (1 + ε) * κ / M - (1 + ε) * Q / M ^ 2 + (1 + ε) * κ / M ^ 2 + 2 * C₁ * κ / M ^ 2
      ≤ (1 + ε) * κ / M + C₂ * κ / M ^ 2 + C₂ / L := by
  have hApos : 0 < 1 + ε := by linarith
  -- The only transcendental input: `k₁ ≤ 1 - e^{-ε} ≤ 0.34 (1 + ε)`.
  have hk' : k₁ ≤ 0.34 * (1 + ε) :=
    le_trans hk1 (one_sub_exp_neg_le ε hε)
  have hk1lt : k₁ < 1 := lt_of_le_of_lt hk1 (by have := Real.exp_pos (-ε); linarith)
  have hM2 : (0 : ℝ) < M ^ 2 := by positivity
  have hκ0 : 0 ≤ κ := by linarith
  have hC2pos : 0 < C₂ := by linarith
  -- `C₂` dominates the coefficient `1001 (1+ε) + 2 C₁`.
  have hC2' : 1001 * (1 + ε) + 2 * C₁ ≤ C₂ := by linarith
  -- The crux, after clearing the denominator `M ^ 2`.
  have hkey : k₁ * M ^ 2 - (1 + ε) * Q + (1 + ε) * κ + 2 * C₁ * κ ≤ C₂ * κ := by
    by_cases hMbig : 15000 ≤ M
    · -- Large `M`: the lower bound `Q ≥ 0.34 M ^ 2 - 1000 κ` and `k₁ ≤ 0.34 (1+ε)` cancel.
      have hQge : 0.34 * M ^ 2 - 1000 * κ ≤ Q := by
        have h1 := hQ0big hMbig
        linarith
      have hkM : k₁ * M ^ 2 ≤ 0.34 * (1 + ε) * M ^ 2 :=
        mul_le_mul_of_nonneg_right hk' (sq_nonneg M)
      have hneg : -((1 + ε) * Q) ≤ -(0.34 * (1 + ε) * M ^ 2) + 1000 * (1 + ε) * κ := by
        have h1 : (1 + ε) * (0.34 * M ^ 2 - 1000 * κ) ≤ (1 + ε) * Q :=
          mul_le_mul_of_nonneg_left hQge hApos.le
        nlinarith only [h1]
      have hmul : (1001 * (1 + ε) + 2 * C₁) * κ ≤ C₂ * κ :=
        mul_le_mul_of_nonneg_right hC2' hκ0
      nlinarith only [hkM, hneg, hmul]
    · -- Small `M`: `Q ≥ -1000 κ` and `M ^ 2 < 15000 ^ 2`, absorbed by `10 ^ 9`.
      have hMlt : M < 15000 := by linarith
      have hQlow : -1000 * κ ≤ Q := by linarith
      have hkM : k₁ * M ^ 2 ≤ M ^ 2 := by nlinarith only [hk1lt, sq_nonneg M]
      have hneg : -((1 + ε) * Q) ≤ 1000 * (1 + ε) * κ := by
        have h1 : (1 + ε) * (-1000 * κ) ≤ (1 + ε) * Q :=
          mul_le_mul_of_nonneg_left hQlow hApos.le
        nlinarith only [h1]
      have hM2lt : M ^ 2 < 225000000 := by nlinarith only [hM, hMlt]
      have hmul : (1001 * (1 + ε) + 2 * C₁ + (10 ^ 9 - 1)) * κ ≤ C₂ * κ := by
        have hc : 1001 * (1 + ε) + 2 * C₁ + (10 ^ 9 - 1) ≤ C₂ := by linarith
        exact mul_le_mul_of_nonneg_right hc hκ0
      nlinarith only [hkM, hneg, hmul, hM2lt, hκ]
  have hgoal1 : k₁ * M ^ 2 - (1 + ε) * Q + (1 + ε) * κ + 2 * C₁ * κ + (1 + ε) * κ * M
      ≤ (1 + ε) * κ * M + C₂ * κ := by
    linarith only [hkey]
  calc
    k₁ + (1 + ε) * κ / M - (1 + ε) * Q / M ^ 2 + (1 + ε) * κ / M ^ 2 + 2 * C₁ * κ / M ^ 2
        = (k₁ * M ^ 2 - (1 + ε) * Q + (1 + ε) * κ + 2 * C₁ * κ + (1 + ε) * κ * M) / M ^ 2 := by
          field_simp
          ring
    _ ≤ ((1 + ε) * κ * M + C₂ * κ) / M ^ 2 := div_le_div_of_nonneg_right hgoal1 hM2.le
    _ = (1 + ε) * κ / M + C₂ * κ / M ^ 2 := by
          field_simp
    _ ≤ (1 + ε) * κ / M + C₂ * κ / M ^ 2 + C₂ / L := by
          have hC2L : 0 ≤ C₂ / L := div_nonneg hC2pos.le hL.le
          linarith

end Work.LinnikAreas.Density4

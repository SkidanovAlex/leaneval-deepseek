import Mathlib
import Submission.Work.LinnikAreas.Density4.cube_mul_exp_neg_le

namespace Work.LinnikAreas.Density4

/-- Arithmetic closing of HB (11.14): the error terms of the three range bounds
(`small_piece_le`, `mid_piece_le`, `far_piece_le`) and of the Abel boundary term, multiplied by `L`,
are bounded by the constant `K`.  Uses `U = e^{uL}` (so `L·L²/U = L³e^{-uL} ≤ 6/u³`, via
`cube_mul_exp_neg_le`), `V = e^{vL}` (so `log(V/U) = (v-u)L`), `1 ≤ V` and `L₁ ≤ L`. -/
theorem final_arith {ε u v x L U V L₁ : ℝ} (hε : 0 < ε) (hu : 0 < u) (hvu : 0 < v - u)
    (hxv : 0 < x - v) (hL : 0 < L) (hL₁pos : 0 < L₁) (hLge : L₁ ≤ L) (hV1 : 1 ≤ V)
    (hUe : U = Real.exp (u*L)) (hVe : V = Real.exp (v*L)) :
    L * (2*L^2/U + 5*(1+ε)/Real.log (V/U) + (1+ε)/(V*Real.log (V/U))
          + (1+ε)/(2*V^2*(Real.log (V/U))^2) + 1/Real.log (V/U)
          + 5/(Real.log (V/U))^2 + 1/(V*(Real.log (V/U))^2)
          + (x-v)*L/(Real.log (V/U))^2)
      ≤ 12/u^3 + 6*(1+ε)/(v-u) + (1+ε)/(2*(v-u)^2*L₁) + 1/(v-u) + 6/((v-u)^2*L₁)
        + (x-v)/(v-u)^2 + 1 := by
  -- `log(V/U) = (v-u)L` from `U = e^{uL}`, `V = e^{vL}`.
  have hVU : V/U = Real.exp ((v-u)*L) := by
    rw [hVe, hUe, ← Real.exp_sub]; congr 1; ring
  have hlog : Real.log (V/U) = (v-u)*L := by rw [hVU, Real.log_exp]
  -- distribute the factor `L` over the eight error terms
  have hdistrib : L * (2*L^2/U + 5*(1+ε)/Real.log (V/U) + (1+ε)/(V*Real.log (V/U))
          + (1+ε)/(2*V^2*(Real.log (V/U))^2) + 1/Real.log (V/U)
          + 5/(Real.log (V/U))^2 + 1/(V*(Real.log (V/U))^2)
          + (x-v)*L/(Real.log (V/U))^2)
      = L*(2*L^2/U) + L*(5*(1+ε)/Real.log (V/U)) + L*((1+ε)/(V*Real.log (V/U)))
          + L*((1+ε)/(2*V^2*(Real.log (V/U))^2)) + L*(1/Real.log (V/U))
          + L*(5/(Real.log (V/U))^2) + L*(1/(V*(Real.log (V/U))^2))
          + L*((x-v)*L/(Real.log (V/U))^2) := by ring
  -- term 1: `L·2L²/U = 2L³e^{-uL} ≤ 12/u³`
  have h1 : L*(2*L^2/U) ≤ 12/u^3 := by
    have hcube := cube_mul_exp_neg_le hu hL.le
    rw [hUe]
    have heq : L * (2*L^2/Real.exp (u*L)) = 2*(L^3 * Real.exp (-(u*L))) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]; ring
    rw [heq]
    have h2 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0:ℝ) ≤ 2)
    have h3 : 2 * (6/u^3) = 12/u^3 := by ring
    linarith [h2, h3]
  -- term 2: `L·5(1+ε)/Λ = 5(1+ε)/(v-u)`
  have h2 : L*(5*(1+ε)/Real.log (V/U)) ≤ 5*(1+ε)/(v-u) := by
    have heq : L*(5*(1+ε)/Real.log (V/U)) = 5*(1+ε)/(v-u) := by rw [hlog]; field_simp
    rw [heq]
  -- term 3: `L·(1+ε)/(VΛ) = (1+ε)/(V(v-u)) ≤ (1+ε)/(v-u)`
  have h3 : L*((1+ε)/(V*Real.log (V/U))) ≤ (1+ε)/(v-u) := by
    have heq : L*((1+ε)/(V*Real.log (V/U))) = (1+ε)/(V*(v-u)) := by rw [hlog]; field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (by linarith) hvu (by nlinarith [hV1, hvu])
  -- term 4: `L·(1+ε)/(2V²Λ²) = (1+ε)/(2V²(v-u)²L) ≤ (1+ε)/(2(v-u)²L₁)`
  have h4 : L*((1+ε)/(2*V^2*(Real.log (V/U))^2)) ≤ (1+ε)/(2*(v-u)^2*L₁) := by
    have hV2 : 1 ≤ V^2 := by nlinarith [hV1]
    have hvu2 : 0 ≤ (v-u)^2 := sq_nonneg _
    have hposL : 0 < (v-u)^2*L := mul_pos (pow_pos hvu 2) hL
    have hstep2 : (v-u)^2*L ≤ V^2*((v-u)^2*L) := by
      calc (v-u)^2*L = 1*((v-u)^2*L) := by ring
        _ ≤ V^2*((v-u)^2*L) := mul_le_mul_of_nonneg_right hV2 hposL.le
    have hden : 2*(v-u)^2*L₁ ≤ 2*V^2*(v-u)^2*L := by
      have h1 : 2*(v-u)^2*L₁ ≤ 2*(v-u)^2*L := by
        have := mul_le_mul_of_nonneg_left hLge hvu2
        linarith
      have h2 : 2*(v-u)^2*L ≤ 2*V^2*((v-u)^2*L) := by linarith [hstep2]
      have h3 : 2*V^2*((v-u)^2*L) = 2*V^2*(v-u)^2*L := by ring
      linarith
    have heq : L*((1+ε)/(2*V^2*(Real.log (V/U))^2)) = (1+ε)/(2*V^2*(v-u)^2*L) := by
      rw [hlog]; field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) hden
  -- term 5: `L/Λ = 1/(v-u)`
  have h5 : L*(1/Real.log (V/U)) ≤ 1/(v-u) := by
    have heq : L*(1/Real.log (V/U)) = 1/(v-u) := by rw [hlog]; field_simp
    rw [heq]
  -- term 6: `L·5/Λ² = 5/((v-u)²L) ≤ 5/((v-u)²L₁)`
  have h6 : L*(5/(Real.log (V/U))^2) ≤ 5/((v-u)^2*L₁) := by
    have hden : (v-u)^2*L₁ ≤ (v-u)^2*L := mul_le_mul_of_nonneg_left hLge (sq_nonneg _)
    have heq : L*(5/(Real.log (V/U))^2) = 5/((v-u)^2*L) := by rw [hlog]; field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  -- term 7: `L/(VΛ²) = 1/(V(v-u)²L) ≤ 1/((v-u)²L₁)`
  have h7 : L*(1/(V*(Real.log (V/U))^2)) ≤ 1/((v-u)^2*L₁) := by
    have hposL : 0 < (v-u)^2*L := mul_pos (pow_pos hvu 2) hL
    have hden : (v-u)^2*L₁ ≤ V*((v-u)^2*L) := by
      have h1 : (v-u)^2*L₁ ≤ (v-u)^2*L := mul_le_mul_of_nonneg_left hLge (sq_nonneg _)
      have h2 : (v-u)^2*L ≤ V*((v-u)^2*L) := by
        calc (v-u)^2*L = 1*((v-u)^2*L) := by ring
          _ ≤ V*((v-u)^2*L) := mul_le_mul_of_nonneg_right hV1 hposL.le
      linarith
    have heq : L*(1/(V*(Real.log (V/U))^2)) = 1/(V*((v-u)^2*L)) := by rw [hlog]; field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  -- term 8: `L·(x-v)L/Λ² = (x-v)/(v-u)²`
  have h8 : L*((x-v)*L/(Real.log (V/U))^2) ≤ (x-v)/(v-u)^2 := by
    have heq : L*((x-v)*L/(Real.log (V/U))^2) = (x-v)/(v-u)^2 := by rw [hlog]; field_simp
    rw [heq]
  -- sum the eight bounds
  have hb : L * (2*L^2/U + 5*(1+ε)/Real.log (V/U) + (1+ε)/(V*Real.log (V/U))
          + (1+ε)/(2*V^2*(Real.log (V/U))^2) + 1/Real.log (V/U)
          + 5/(Real.log (V/U))^2 + 1/(V*(Real.log (V/U))^2)
          + (x-v)*L/(Real.log (V/U))^2)
      ≤ 12/u^3 + 5*(1+ε)/(v-u) + (1+ε)/(v-u) + (1+ε)/(2*(v-u)^2*L₁)
        + 1/(v-u) + 5/((v-u)^2*L₁) + 1/((v-u)^2*L₁) + (x-v)/(v-u)^2 := by
    rw [hdistrib]
    linarith [h1, h2, h3, h4, h5, h6, h7, h8]
  -- combine like terms; the `+1` on the right is pure slack
  have htarget : (12/u^3 + 5*(1+ε)/(v-u) + (1+ε)/(v-u) + (1+ε)/(2*(v-u)^2*L₁)
        + 1/(v-u) + 5/((v-u)^2*L₁) + 1/((v-u)^2*L₁) + (x-v)/(v-u)^2)
      = (12/u^3 + 6*(1+ε)/(v-u) + (1+ε)/(2*(v-u)^2*L₁) + 1/(v-u) + 6/((v-u)^2*L₁)
        + (x-v)/(v-u)^2 + 1) - 1 := by ring
  linarith [hb, htarget]

end Work.LinnikAreas.Density4

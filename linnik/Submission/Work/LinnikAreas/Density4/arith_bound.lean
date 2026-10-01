import Mathlib

namespace Work.LinnikAreas.Density4

/-- Elementary arithmetic core: for `0 ≤ A1 ≤ 4U`, `0 ≤ A2 ≤ 16U²`, `0 ≤ A3 ≤ 64U³`,
`0 ≤ c ≤ 2U` and `1 ≤ U`, the bracket
`(1+A1)c³ + (6c²A1 + 24cA2 + 48A3)(1+2A1)` is at most `4·10⁴·U⁴`. -/
private lemma bracket_aux {A1 A2 A3 c U : ℝ} (hA10 : 0 ≤ A1) (hA1 : A1 ≤ 4*U)
    (hA20 : 0 ≤ A2) (hA2 : A2 ≤ 16*U^2) (hA30 : 0 ≤ A3) (hA3 : A3 ≤ 64*U^3)
    (hc0 : 0 ≤ c) (hc2U : c ≤ 2*U) (hU1 : 1 ≤ U) :
    (1 + A1)*c^3 + (6*c^2*A1 + 24*c*A2 + 48*A3)*(1 + 2*A1) ≤ 40000*U^4 := by
  have hU0 : 0 ≤ U := by linarith
  have hc3 : c^3 ≤ 8*U^3 := by
    have := pow_le_pow_left₀ hc0 hc2U 3; nlinarith [this]
  have hc2 : c^2 ≤ 4*U^2 := by
    have := pow_le_pow_left₀ hc0 hc2U 2; nlinarith [this]
  have hp1 : A1*c^3 ≤ 32*U^4 := by
    have h := mul_le_mul hA1 hc3 (pow_nonneg hc0 3) (by positivity : (0:ℝ) ≤ 4*U)
    nlinarith [h]
  have hp2 : c^2*A1 ≤ 16*U^3 := by
    have h := mul_le_mul hc2 hA1 hA10 (by positivity : (0:ℝ) ≤ 4*U^2)
    nlinarith [h]
  have hp3 : c*A2 ≤ 32*U^3 := by
    have h := mul_le_mul hc2U hA2 hA20 (by positivity : (0:ℝ) ≤ 2*U)
    nlinarith [h]
  have h1A1 : 1 + 2*A1 ≤ 9*U := by linarith
  have h1A10 : 0 ≤ 1 + 2*A1 := by linarith
  have hS : 6*c^2*A1 + 24*c*A2 + 48*A3 ≤ 3936*U^3 := by nlinarith [hp2, hp3, hA3]
  have hp5 : (6*c^2*A1 + 24*c*A2 + 48*A3)*(1+2*A1) ≤ 3936*U^3*(9*U) :=
    mul_le_mul hS h1A1 h1A10 (by positivity)
  have ht1 : (1+A1)*c^3 ≤ 8*U^3 + 32*U^4 := by nlinarith [hc3, hp1]
  nlinarith [ht1, hp5, hU1]

/-- **Arithmetic closure of the `Sbig` tail estimate.** With `L = log q ≥ log 2`, `U = e^{uL} ≥ 1`
(`u > 0`), `a = L²/U` and `0 ≤ c ≤ U+1`, one has
`L·e^{-L²}·[(1+1/a)c³ + (6c²/a + 24c/a² + 48/a³)(1+2/a)] ≤ 10^6·e^{8u²}`.
Proof sketch: `c ≤ U+1 ≤ 2U` and `U ≥ 1` give `c^3 ≤ 8U^3 ≤ 8U^4`, `1/a = U/L²`, `1/a² = U²/L⁴`,
`1/a³ = U³/L⁶`, and `1/L^k ≤ 2^k` for `k ≤ 8` (since `L ≥ log 2 > 1/2`), so the bracket is at most
`~3.6·10⁴·U⁴`; then `L·e^{-L²}·U⁴ = L·e^{4uL-L²} ≤ e^{8u²}·L·e^{-L²/2} ≤ e^{8u²}` because
`4uL - L² ≤ 8u² - L²/2` and `L ≤ e^{L²/2}` for `L ≥ 0` (from `log L ≤ L - 1 ≤ L²/2`). -/
lemma arith_bound {u L c a U : ℝ} (hu : 0 < u) (hL : Real.log 2 ≤ L) (hU1 : 1 ≤ U)
    (hUL : U = Real.exp (u * L)) (ha : a = L^2/U) (hc0 : 0 ≤ c) (hc : c ≤ U + 1) :
    L * (Real.exp (-(L^2)) * ((1 + 1/a) * c^3 + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1 + 2/a)))
      ≤ 1000000 * Real.exp (8*u^2) := by
  have hLhalf : (1:ℝ)/2 ≤ L := by linarith [Real.log_two_gt_d9]
  have hLpos : 0 < L := by linarith
  have hUpos : 0 < U := by linarith
  have hLsq : (1:ℝ)/4 ≤ L^2 := by nlinarith [sq_nonneg (L - 1/2), hLhalf]
  have hapos : 0 < a := by rw [ha]; positivity
  -- the bracket
  have hc2U : c ≤ 2*U := by linarith
  have hA0 : 0 ≤ 1/a := by positivity
  have hA1 : 1/a ≤ 4*U := by
    rw [ha, one_div_div, div_le_iff₀ (pow_pos hLpos 2)]
    nlinarith [hLsq, hUpos.le]
  have hA2 : 1/a^2 ≤ 16*U^2 := by
    rw [← one_div_pow]; have := pow_le_pow_left₀ hA0 hA1 2; nlinarith [this]
  have hA3 : 1/a^3 ≤ 64*U^3 := by
    rw [← one_div_pow]; have := pow_le_pow_left₀ hA0 hA1 3; nlinarith [this]
  have hA20 : 0 ≤ 1/a^2 := by positivity
  have hA30 : 0 ≤ 1/a^3 := by positivity
  have hbr : (1 + 1/a) * c^3 + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1 + 2/a) ≤ 40000 * U^4 := by
    have key := bracket_aux (A1 := 1/a) (A2 := 1/a^2) (A3 := 1/a^3)
      hA0 hA1 hA20 hA2 hA30 hA3 hc0 hc2U hU1
    rw [show (1 + 1/a)*c^3 + (6*c^2/a + 24*c/a^2 + 48/a^3)*(1+2/a)
        = (1 + 1/a)*c^3 + (6*c^2*(1/a) + 24*c*(1/a^2) + 48*(1/a^3))*(1+2*(1/a)) from by ring]
    exact key
  -- `L·e^{-L²}·U⁴ ≤ e^{8u²}`
  have hexp_eq : Real.exp (-(L^2)) * U^4 = Real.exp (4*(u*L) - L^2) := by
    have h1 : U^4 = Real.exp (4*(u*L)) := by rw [hUL, ← Real.exp_nat_mul]; norm_num
    rw [h1, ← Real.exp_add]
    congr 1
    ring
  have hL_le : L ≤ Real.exp (L^2/2) := by
    have h1 : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
    have h2 : L - 1 ≤ L^2/2 := by nlinarith [sq_nonneg (L - 1)]
    have h3 : Real.log L ≤ L^2/2 := le_trans h1 h2
    have := Real.exp_le_exp.mpr h3
    rwa [Real.exp_log hLpos] at this
  have hexp : L * Real.exp (-(L^2)) * U^4 ≤ Real.exp (8*u^2) := by
    calc L * Real.exp (-(L^2)) * U^4
        = L * Real.exp (4*(u*L) - L^2) := by rw [mul_assoc, hexp_eq]
      _ ≤ Real.exp (L^2/2) * Real.exp (4*(u*L) - L^2) :=
          mul_le_mul_of_nonneg_right hL_le (Real.exp_pos _).le
      _ = Real.exp (L^2/2 + (4*(u*L) - L^2)) := by rw [Real.exp_add]
      _ = Real.exp (4*u*L - L^2/2) := by congr 1; ring
      _ ≤ Real.exp (8*u^2) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (u - L/4)])
  -- assembly
  calc L * (Real.exp (-(L^2)) * ((1 + 1/a) * c^3 + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1 + 2/a)))
      = L * Real.exp (-(L^2)) * ((1 + 1/a) * c^3 + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1 + 2/a)) := by ring
    _ ≤ L * Real.exp (-(L^2)) * (40000*U^4) :=
        mul_le_mul_of_nonneg_left hbr (by positivity)
    _ = 40000 * (L * Real.exp (-(L^2)) * U^4) := by ring
    _ ≤ 40000 * Real.exp (8*u^2) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ 1000000 * Real.exp (8*u^2) := by
        have := (Real.exp_pos (8*u^2)).le
        nlinarith [this]

end Work.LinnikAreas.Density4

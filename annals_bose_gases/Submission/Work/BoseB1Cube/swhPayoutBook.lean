import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.BoseB1Cube

/-- Pure-real payout bookkeeping.

Writing `A = √(M₂K Pc / (2V²))`, `b = √(D/2)`, `x = √(8kμV/(3(S-1)))`,
`y = √(16 K_w n Q V²/(3W(S²-S)))` and `κ = 3WS(S-1)/(8V²)`:

* `k μ W S / V = κ x²` and `κ ≤ A²` because `M₂K Pc ≥ (3/4)W(S²-S)` — so the left side is
  `κ x² ≤ A²x² = (A x)²`;
* `b² = D/2 ≤ 2K_w n Q ≤ A²y² = (Ay)²`, so `b ≤ Ay`;
* hence `A - b ≥ A(1-y) ≥ Ax ≥ 0` by `x + y ≤ 1`, and squaring gives `(A-b)² ≥ (Ax)²`. -/
theorem swhPayoutBook {V W S Q n Kw D M2K Pc k μ : ℝ}
    (hV : 0 < V) (hW : 0 < W) (hS : 1 < S) (hQ : 0 ≤ Q) (hn : 0 ≤ n)
    (hKw : 0 ≤ Kw) (hk : 0 ≤ k) (hμ : 0 < μ)
    (hM2K : (3 / 4) * W ≤ M2K) (hPc : S ^ 2 - S ≤ Pc)
    (hD0 : 0 ≤ D) (hD : D ≤ 4 * Kw * (n - 1) * Q)
    (hSqrt : Real.sqrt (8 * k * μ * V / (3 * (S - 1)))
        + Real.sqrt (16 * Kw * n * Q * V ^ 2 / (3 * W * (S ^ 2 - S))) ≤ 1) :
    k * μ * W * S / V ≤ (Real.sqrt (M2K * Pc / (2 * V ^ 2)) - Real.sqrt (D / 2)) ^ 2 := by
  set A := Real.sqrt (M2K * Pc / (2 * V ^ 2)) with hA
  set b := Real.sqrt (D / 2) with hb
  set x := Real.sqrt (8 * k * μ * V / (3 * (S - 1))) with hx
  set y := Real.sqrt (16 * Kw * n * Q * V ^ 2 / (3 * W * (S ^ 2 - S))) with hy
  have hS1 : 0 < S - 1 := by linarith
  have hSsq : 0 < S ^ 2 - S := by nlinarith [hS]
  have hV2 : (0:ℝ) < V ^ 2 := by positivity
  have hM2Knn : 0 ≤ M2K := by nlinarith [hW, hM2K]
  have hPcnn : 0 ≤ Pc := by nlinarith [hS, hPc]
  have hkμV : 0 ≤ 8 * k * μ * V := by
    have h8k : (0:ℝ) ≤ 8 * k := by linarith [hk]
    exact mul_nonneg (mul_nonneg h8k (le_of_lt hμ)) (le_of_lt hV)
  have hden1 : 0 ≤ 3 * (S - 1) := by linarith [hS1]
  have hd1 : 0 ≤ 8 * k * μ * V / (3 * (S - 1)) := div_nonneg hkμV hden1
  have hnum2 : 0 ≤ 16 * Kw * n * Q * V ^ 2 := by
    have h1 : 0 ≤ 16 * Kw := by linarith [hKw]
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hn) hQ) (sq_nonneg V)
  have hden2 : 0 ≤ 3 * W * (S ^ 2 - S) := by
    have h1 : (0:ℝ) ≤ 3 * W := by linarith [hW]
    exact mul_nonneg h1 (le_of_lt hSsq)
  have hd2 : 0 ≤ 16 * Kw * n * Q * V ^ 2 / (3 * W * (S ^ 2 - S)) := div_nonneg hnum2 hden2
  have hd3 : 0 ≤ M2K * Pc / (2 * V ^ 2) := div_nonneg (mul_nonneg hM2Knn hPcnn) (by positivity)
  have hd4 : 0 ≤ D / 2 := div_nonneg hD0 (by norm_num)
  have hx2 : x ^ 2 = 8 * k * μ * V / (3 * (S - 1)) := by rw [hx]; exact Real.sq_sqrt hd1
  have hy2 : y ^ 2 = 16 * Kw * n * Q * V ^ 2 / (3 * W * (S ^ 2 - S)) := by
    rw [hy]; exact Real.sq_sqrt hd2
  have hA2 : A ^ 2 = M2K * Pc / (2 * V ^ 2) := by rw [hA]; exact Real.sq_sqrt hd3
  have hb2 : b ^ 2 = D / 2 := by rw [hb]; exact Real.sq_sqrt hd4
  have hAnn : 0 ≤ A := by rw [hA]; exact Real.sqrt_nonneg _
  have hbnn : 0 ≤ b := by rw [hb]; exact Real.sqrt_nonneg _
  have hxnn : 0 ≤ x := by rw [hx]; exact Real.sqrt_nonneg _
  have hynn : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  set κ := 3 * W * S * (S - 1) / (8 * V ^ 2) with hκ
  -- `M₂K Pc ≥ (3/4) W (S²-S)`, cleared of denominators
  have hMP : (3 / 4) * W * (S ^ 2 - S) ≤ M2K * Pc := by
    have h1 : (3 / 4) * W * (S ^ 2 - S) ≤ M2K * (S ^ 2 - S) :=
      mul_le_mul_of_nonneg_right hM2K (le_of_lt hSsq)
    have h2 : M2K * (S ^ 2 - S) ≤ M2K * Pc := mul_le_mul_of_nonneg_left hPc hM2Knn
    linarith
  have hMP4 : 3 * W * S * (S - 1) ≤ 4 * M2K * Pc := by nlinarith [hMP]
  -- the key lower bound on `A²`
  have hK1 : κ ≤ A ^ 2 := by
    rw [hκ, hA2]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * V ^ 2) (by positivity : (0:ℝ) < 2 * V ^ 2)]
    nlinarith [hMP4, hV2]
  -- `k μ W S / V = κ x²`
  have hLHS : k * μ * W * S / V = κ * x ^ 2 := by
    rw [hx2, hκ]; field_simp
  -- `κ y² = 2 K_w n Q`
  have hKy : κ * y ^ 2 = 2 * Kw * n * Q := by
    rw [hy2, hκ]; field_simp; ring
  have hK2 : 2 * Kw * n * Q ≤ A ^ 2 * y ^ 2 := by
    rw [← hKy]
    exact mul_le_mul_of_nonneg_right hK1 (sq_nonneg y)
  -- `b² = D/2 ≤ 2 K_w n Q`
  have hKnQ : 0 ≤ Kw * Q := mul_nonneg hKw hQ
  have hDle : D ≤ 4 * Kw * n * Q := by nlinarith [hD, hKnQ]
  have hb2le : b ^ 2 ≤ 2 * Kw * n * Q := by nlinarith [hb2, hDle]
  have hAy_sq : b ^ 2 ≤ (A * y) ^ 2 := by nlinarith [hb2le, hK2]
  have hAy_nn : 0 ≤ A * y := mul_nonneg hAnn hynn
  have hb_le_Ay : b ≤ A * y := by
    have hbm : b * b ≤ (A * y) * (A * y) := by simpa only [pow_two] using hAy_sq
    exact (mul_self_le_mul_self_iff hbnn hAy_nn).mpr hbm
  -- `A - b ≥ A x ≥ 0`
  have hx_le : x ≤ 1 - y := by linarith [hSqrt]
  have hAx_le : A * x ≤ A * (1 - y) := mul_le_mul_of_nonneg_left hx_le hAnn
  have hAxb : A * x ≤ A - b := by nlinarith [hAx_le, hb_le_Ay]
  have hAxnn : 0 ≤ A * x := mul_nonneg hAnn hxnn
  have h1 : κ * x ^ 2 ≤ A ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_right hK1 (sq_nonneg x)
  have hsum : 0 ≤ (A - b) + A * x := by linarith [hAxb, hAxnn]
  have hsq : (A * x) ^ 2 ≤ (A - b) ^ 2 := by nlinarith [hAxb, hsum]
  have hmain : κ * x ^ 2 ≤ (A - b) ^ 2 := by
    calc κ * x ^ 2 ≤ A ^ 2 * x ^ 2 := h1
      _ = (A * x) ^ 2 := by ring
      _ ≤ (A - b) ^ 2 := hsq
  exact hLHS.symm ▸ hmain

end Work.BoseB1Cube

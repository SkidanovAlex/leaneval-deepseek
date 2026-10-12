import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseGateFS

/-- The RHS of the target is a product of a coefficient with `μ * a ^ 3 * KH ^ 2 * s`;
this auxiliary identity rewrites that tail using `s = KH * a`. -/
private lemma arith_lip_const_rhs {Cw Cg Cτ cτ μ a KH s : ℝ} (ha : 0 < a)
    (hsa : s = KH * a) :
    10 ^ 12 * (Cw + Cg + Cτ + 1) ^ 4 * (1 + 1 / cτ) ^ 4 * (1 + 1 / a) ^ 4
        * (μ * a ^ 3 * KH ^ 2) * s
      = 10 ^ 12 * (Cw + Cg + Cτ + 1) ^ 4 * (1 + 1 / cτ) ^ 4 * (1 + 1 / a) ^ 4
        * (μ * a * s ^ 3) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hKH : KH = s / a := by
    rw [eq_div_iff ha0]
    exact hsa.symm
  have hP : μ * a ^ 3 * KH ^ 2 = μ * a * s ^ 2 := by
    rw [hKH]
    field_simp
  rw [hP]
  ring

theorem arith_lip_const {Cw Cg Cτ cτ ρ μ a KH s : ℝ}
    (hCw : 0 ≤ Cw) (hCg : 0 ≤ Cg) (hCτ : 0 ≤ Cτ) (hcτ : 0 < cτ)
    (ha : 0 < a) (hμ : 0 ≤ μ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 3 * μ / 2)
    (hs : 1 ≤ s) (hsa : s = KH * a) :
    192 * ρ * Cg * a * s ^ 2 + 2048 * ρ * Cw * a * Cτ * s ^ 3 ≤
      10 ^ 12 * (Cw + Cg + Cτ + 1) ^ 4 * (1 + 1 / cτ) ^ 4 * (1 + 1 / a) ^ 4
        * (μ * a ^ 3 * KH ^ 2) * s := by
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  rw [arith_lip_const_rhs ha hsa]
  -- abbreviations for the two remaining compound expressions
  set B := Cw + Cg + Cτ + 1 with hBdef
  set D1 := 1 + 1 / cτ with hD1def
  set D2 := 1 + 1 / a with hD2def
  have hB1 : (0 : ℝ) ≤ B := by rw [hBdef]; linarith
  have hBge1 : (1 : ℝ) ≤ B := by rw [hBdef]; linarith
  have hD1n : (0 : ℝ) ≤ D1 := by
    rw [hD1def]
    have : (0 : ℝ) < 1 / cτ := div_pos one_pos hcτ
    linarith
  have hD2n : (0 : ℝ) ≤ D2 := by
    rw [hD2def]
    have : (0 : ℝ) < 1 / a := div_pos one_pos ha
    linarith
  have hD1ge : (1 : ℝ) ≤ D1 ^ 4 := by
    have h1 : (1 : ℝ) ≤ D1 := by
      rw [hD1def]
      have : (0 : ℝ) < 1 / cτ := div_pos one_pos hcτ
      linarith
    calc (1 : ℝ) = (1 : ℝ) ^ 4 := by norm_num
      _ ≤ D1 ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
  have hD2ge : (1 : ℝ) ≤ D2 ^ 4 := by
    have h1 : (1 : ℝ) ≤ D2 := by
      rw [hD2def]
      have : (0 : ℝ) < 1 / a := div_pos one_pos ha
      linarith
    calc (1 : ℝ) = (1 : ℝ) ^ 4 := by norm_num
      _ ≤ D2 ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
  have hB4n : (0 : ℝ) ≤ B ^ 4 := pow_nonneg hB1 4
  have hBsq_nn : (0 : ℝ) ≤ B ^ 2 := pow_nonneg hB1 2
  have hCgleB : Cg ≤ B := by rw [hBdef]; linarith
  have hCwleB : Cw ≤ B := by rw [hBdef]; linarith
  have hCτleB : Cτ ≤ B := by rw [hBdef]; linarith
  have hBsqCg : Cg ≤ B ^ 2 := by
    calc Cg = Cg * 1 := by ring
      _ ≤ B * B := mul_le_mul hCgleB hBge1 zero_le_one hB1
      _ = B ^ 2 := by ring
  have hBsqCw : Cw ≤ B ^ 2 := by
    calc Cw = Cw * 1 := by ring
      _ ≤ B * B := mul_le_mul hCwleB hBge1 zero_le_one hB1
      _ = B ^ 2 := by ring
  have hBsqCτ : Cτ ≤ B ^ 2 := by
    calc Cτ = Cτ * 1 := by ring
      _ ≤ B * B := mul_le_mul hCτleB hBge1 zero_le_one hB1
      _ = B ^ 2 := by ring
  have hBsq1 : (1 : ℝ) ≤ B ^ 2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ B * B := mul_le_mul hBge1 hBge1 zero_le_one hB1
      _ = B ^ 2 := by ring
  have hbase1 : Cg ≤ B ^ 4 := by
    calc Cg = Cg * 1 := by ring
      _ ≤ B ^ 2 * B ^ 2 := mul_le_mul hBsqCg hBsq1 zero_le_one hBsq_nn
      _ = B ^ 4 := by ring
  have hbase2 : Cw * Cτ ≤ B ^ 4 := by
    calc Cw * Cτ ≤ B ^ 2 * B ^ 2 := mul_le_mul hBsqCw hBsqCτ hCτ hBsq_nn
      _ = B ^ 4 := by ring
  have hN : (0 : ℝ) ≤ μ * a * s ^ 3 :=
    mul_nonneg (mul_nonneg hμ (le_of_lt ha)) (pow_nonneg hs0 3)
  have hs23 : s ^ 2 ≤ s ^ 3 := by
    calc s ^ 2 = s ^ 2 * 1 := by ring
      _ ≤ s ^ 2 * s := mul_le_mul_of_nonneg_left hs (pow_nonneg hs0 2)
      _ = s ^ 3 := by ring
  -- first summand of the left-hand side
  have hA : 192 * ρ * Cg * a * s ^ 2 ≤ 288 * μ * Cg * a * s ^ 3 := by
    have h1 : ρ * (Cg * a * s ^ 2) ≤ (3 * μ / 2) * (Cg * a * s ^ 2) :=
      mul_le_mul_of_nonneg_right hρ
        (mul_nonneg (mul_nonneg hCg (le_of_lt ha)) (pow_nonneg hs0 2))
    have h2 : (3 * μ / 2) * (Cg * a * s ^ 2) ≤ (3 * μ / 2) * (Cg * a * s ^ 3) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs23 (mul_nonneg hCg (le_of_lt ha)))
        (by linarith : (0 : ℝ) ≤ 3 * μ / 2)
    calc 192 * ρ * Cg * a * s ^ 2 = 192 * (ρ * (Cg * a * s ^ 2)) := by ring
      _ ≤ 192 * ((3 * μ / 2) * (Cg * a * s ^ 3)) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) (by norm_num)
      _ = 288 * μ * Cg * a * s ^ 3 := by ring
  -- second summand of the left-hand side
  have hBc : 2048 * ρ * Cw * a * Cτ * s ^ 3 ≤ 3072 * μ * (Cw * Cτ) * a * s ^ 3 := by
    have h1 : ρ * ((Cw * Cτ) * a * s ^ 3) ≤ (3 * μ / 2) * ((Cw * Cτ) * a * s ^ 3) :=
      mul_le_mul_of_nonneg_right hρ
        (mul_nonneg (mul_nonneg (mul_nonneg hCw hCτ) (le_of_lt ha)) (pow_nonneg hs0 3))
    calc 2048 * ρ * Cw * a * Cτ * s ^ 3 = 2048 * (ρ * ((Cw * Cτ) * a * s ^ 3)) := by ring
      _ ≤ 2048 * ((3 * μ / 2) * ((Cw * Cτ) * a * s ^ 3)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 3072 * μ * (Cw * Cτ) * a * s ^ 3 := by ring
  have h12 : (1 : ℝ) ≤ D1 ^ 4 * D2 ^ 4 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ D1 ^ 4 * D2 ^ 4 := mul_le_mul hD1ge hD2ge zero_le_one (pow_nonneg hD1n 4)
  -- the two summands together are dominated by the right-hand side
  have hmain : 288 * μ * Cg * a * s ^ 3 + 3072 * μ * (Cw * Cτ) * a * s ^ 3 ≤
      10 ^ 12 * B ^ 4 * D1 ^ 4 * D2 ^ 4 * (μ * a * s ^ 3) := by
    have hcoef : 288 * Cg + 3072 * (Cw * Cτ) ≤ 10 ^ 12 * B ^ 4 := by
      have h1 : 288 * Cg ≤ 288 * B ^ 4 := mul_le_mul_of_nonneg_left hbase1 (by norm_num)
      have h3 : 3072 * (Cw * Cτ) ≤ 3072 * B ^ 4 :=
        mul_le_mul_of_nonneg_left hbase2 (by norm_num)
      have h4 : (3360 : ℝ) * B ^ 4 ≤ 10 ^ 12 * B ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num) hB4n
      linarith
    have hstep1 : (288 * Cg + 3072 * (Cw * Cτ)) * (μ * a * s ^ 3) ≤
        (10 ^ 12 * B ^ 4) * (μ * a * s ^ 3) := mul_le_mul_of_nonneg_right hcoef hN
    have hstep2 : (10 ^ 12 * B ^ 4) * (μ * a * s ^ 3) ≤
        10 ^ 12 * B ^ 4 * D1 ^ 4 * D2 ^ 4 * (μ * a * s ^ 3) := by
      have h0 : (0 : ℝ) ≤ (10 ^ 12 * B ^ 4) * (μ * a * s ^ 3) :=
        mul_nonneg (mul_nonneg (by norm_num) hB4n) hN
      calc (10 ^ 12 * B ^ 4) * (μ * a * s ^ 3)
          = ((10 ^ 12 * B ^ 4) * (μ * a * s ^ 3)) * 1 := by ring
        _ ≤ ((10 ^ 12 * B ^ 4) * (μ * a * s ^ 3)) * (D1 ^ 4 * D2 ^ 4) :=
            mul_le_mul_of_nonneg_left h12 h0
        _ = 10 ^ 12 * B ^ 4 * D1 ^ 4 * D2 ^ 4 * (μ * a * s ^ 3) := by ring
    calc 288 * μ * Cg * a * s ^ 3 + 3072 * μ * (Cw * Cτ) * a * s ^ 3
        = (288 * Cg + 3072 * (Cw * Cτ)) * (μ * a * s ^ 3) := by ring
      _ ≤ (10 ^ 12 * B ^ 4) * (μ * a * s ^ 3) := hstep1
      _ ≤ 10 ^ 12 * B ^ 4 * D1 ^ 4 * D2 ^ 4 * (μ * a * s ^ 3) := hstep2
  exact le_trans (add_le_add hA hBc) hmain

end Work.BoseGateFS

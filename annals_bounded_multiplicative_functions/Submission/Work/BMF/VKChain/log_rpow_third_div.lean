import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKChain

/-- For `x ≥ exp 1000`, `Real.log x ≤ x ^ (1/3) / 10^9`. -/
lemma log_rpow_third_div {x : ℝ} (hx : Real.exp 1000 ≤ x) :
    Real.log x ≤ x ^ (1 / 3 : ℝ) / 10 ^ 9 := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1000) hx
  have hxnonneg : 0 ≤ x := hxpos.le
  -- General (crude) bound `log x ≤ 4 x^{1/4}`.
  have hlog : Real.log x ≤ 4 * x ^ ((1:ℝ)/4) := by
    have h := Real.log_le_rpow_div hxnonneg (show (0:ℝ) < 1/4 by norm_num)
    calc Real.log x ≤ x ^ ((1:ℝ)/4) / (1/4) := h
      _ = 4 * x ^ ((1:ℝ)/4) := by ring
  -- Numerics: `4·10^9 ≤ exp 32`, via `exp 32 = (exp 1)^32 ≥ 2^32`.
  have hpow : (2:ℝ)^32 ≤ Real.exp 32 := by
    have h1 : Real.exp 32 = (Real.exp 1)^32 := by
      rw [show (32:ℝ) = ((32:ℕ):ℝ) * 1 by norm_num]
      exact Real.exp_nat_mul 1 32
    rw [h1]
    exact pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_two) 32
  -- `4·10^9 ≤ x^{1/12}` since `x^{1/12} ≥ exp(1000/12) ≥ exp 32`.
  have h12 : (4 * 10^9 : ℝ) ≤ x ^ ((1:ℝ)/12) := by
    have hmono : (Real.exp 1000) ^ ((1:ℝ)/12) ≤ x ^ ((1:ℝ)/12) :=
      Real.rpow_le_rpow (Real.exp_pos 1000).le hx (by norm_num)
    rw [← Real.exp_mul] at hmono
    have hmono2 : Real.exp 32 ≤ Real.exp (1000 * (1/12)) :=
      Real.exp_le_exp.mpr (by norm_num)
    have hnum : (4 * 10^9 : ℝ) ≤ (2:ℝ)^32 := by norm_num
    linarith
  have hx14 : 0 ≤ x ^ ((1:ℝ)/4) := Real.rpow_nonneg hxnonneg _
  -- `10^9 · log x ≤ x^{1/3}`.
  have hstep : Real.log x * 10^9 ≤ x ^ (1/3:ℝ) := by
    have h4 : x ^ ((1:ℝ)/12) * x ^ ((1:ℝ)/4) = x ^ (1/3:ℝ) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    calc Real.log x * 10^9 ≤ 4 * x ^ ((1:ℝ)/4) * 10^9 :=
          mul_le_mul_of_nonneg_right hlog (by norm_num)
      _ = (4*10^9 : ℝ) * x ^ ((1:ℝ)/4) := by ring
      _ ≤ x ^ ((1:ℝ)/12) * x ^ ((1:ℝ)/4) := mul_le_mul_of_nonneg_right h12 hx14
      _ = x ^ (1/3:ℝ) := h4
  rw [le_div_iff₀ (show (0:ℝ) < 10^9 by norm_num)]
  exact hstep

end Work.BMF.VKChain

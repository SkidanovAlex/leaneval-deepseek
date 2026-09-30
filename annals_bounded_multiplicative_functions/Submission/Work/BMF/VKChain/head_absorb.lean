import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKChain

/-- Absorption of the head term into the shape `(a^{-σ} + L^{6/7})`. -/
theorem head_absorb {cvk L a σ : ℝ} (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1)
    (hσ : 0 < σ) (hL : 1 ≤ L) :
    a ^ (-σ) + 2 * (Real.exp 4 * 5) * (2 + (L / cvk) ^ (6 / 7 : ℝ)) ≤
      (1 + 10 * Real.exp 4 * (2 + cvk ^ (-(6 / 7) : ℝ))) * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) := by
  -- The head term `a^{-σ} ≥ 1` because `0 < a ≤ 1` and `σ > 0`.
  have hA : 1 ≤ a ^ (-σ) := by
    have h := Real.rpow_le_rpow_of_nonpos ha ha1 (show (-σ) ≤ 0 by linarith)
    rwa [Real.one_rpow] at h
  have hq : 0 ≤ L ^ (6 / 7 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hr : 0 ≤ cvk ^ (-(6 / 7) : ℝ) := Real.rpow_nonneg (le_of_lt hcvk0) _
  have he : 0 < Real.exp 4 := Real.exp_pos 4
  -- Split the product `(L/cvk)^{6/7} = L^{6/7} · cvk^{-6/7}`.
  have hxy : (L / cvk) ^ (6 / 7 : ℝ) = L ^ (6 / 7 : ℝ) * cvk ^ (-(6 / 7) : ℝ) := by
    rw [Real.div_rpow (by linarith) (le_of_lt hcvk0), Real.rpow_neg (le_of_lt hcvk0),
      div_eq_mul_inv]
  rw [hxy]
  -- After the substitution the goal is polynomial in `a^{-σ}, L^{6/7}, cvk^{-6/7}, exp 4`.
  have h1 : (0:ℝ) ≤ Real.exp 4 * (a ^ (-σ) - 1) := mul_nonneg he.le (by linarith)
  have h2 : (0:ℝ) ≤ Real.exp 4 * L ^ (6 / 7 : ℝ) := mul_nonneg he.le hq
  have h3 : (0:ℝ) ≤ Real.exp 4 * (cvk ^ (-(6 / 7) : ℝ)) * (a ^ (-σ)) :=
    mul_nonneg (mul_nonneg he.le hr) (by linarith)
  nlinarith [h1, h2, h3, hA, hq, hr, he]

end Work.BMF.VKChain

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

/-- For every nonnegative real `x`, `Real.log x ≤ Real.sqrt x`.

The proof rewrites `log x = 4 log (x^{1/4})`, bounds `log (x^{1/4}) ≤ x^{1/4} - 1`
and uses `4 (u - 1) ≤ u ^ 2` (which is `(u - 2) ^ 2 ≥ 0`) for `u = x^{1/4}`,
so that `(x^{1/4}) ^ 2 = sqrt x`. -/
lemma log_le_sqrt_of_nonneg (x : ℝ) (hx : 0 ≤ x) : Real.log x ≤ Real.sqrt x := by
  rcases hx.eq_or_lt with hx0 | hx0
  · rw [← hx0]; simp [Real.log_zero]
  · have hu : 0 < x ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hx0 _
    have h1 : Real.log (x ^ ((1:ℝ)/4)) ≤ x ^ ((1:ℝ)/4) - 1 := Real.log_le_sub_one_of_pos hu
    have h2 : 4 * (x ^ ((1:ℝ)/4) - 1) ≤ (x ^ ((1:ℝ)/4))^2 := by
      nlinarith [sq_nonneg (x ^ ((1:ℝ)/4) - 2)]
    have hsq : (x ^ ((1:ℝ)/4))^2 = Real.sqrt x := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_mul hx ((1:ℝ)/4) 2]
      norm_num
    have hlogx : Real.log x = 4 * Real.log (x ^ ((1:ℝ)/4)) := by
      have := Real.log_rpow hx0 ((1:ℝ)/4); linarith
    calc Real.log x = 4 * Real.log (x ^ ((1:ℝ)/4)) := hlogx
      _ ≤ 4 * (x ^ ((1:ℝ)/4) - 1) := by linarith
      _ ≤ (x ^ ((1:ℝ)/4))^2 := h2
      _ = Real.sqrt x := hsq

theorem log_mul_rpow_neg_le {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 1 ≤ σ) :
    Real.log (n : ℝ) * (n : ℝ) ^ (-2 * σ) ≤ (n : ℝ) ^ (-(3 : ℝ) / 2) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hlog : Real.log (n:ℝ) ≤ (n:ℝ) ^ ((1:ℝ)/2) := by
    have h := log_le_sqrt_of_nonneg (n:ℝ) (le_of_lt hnpos)
    rwa [Real.sqrt_eq_rpow] at h
  have hx2s : (0:ℝ) ≤ (n:ℝ) ^ (-2 * σ) := Real.rpow_nonneg (le_of_lt hnpos) _
  have hexp : (1:ℝ)/2 + (-2*σ) ≤ -(3:ℝ)/2 := by linarith
  calc Real.log (n:ℝ) * (n:ℝ)^(-2*σ)
      ≤ (n:ℝ)^((1:ℝ)/2) * (n:ℝ)^(-2*σ) := mul_le_mul_of_nonneg_right hlog hx2s
    _ = (n:ℝ)^((1:ℝ)/2 + (-2*σ)) := (Real.rpow_add hnpos _ _).symm
    _ ≤ (n:ℝ)^(-(3:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hn1 hexp

end Work.BMF.mrlas

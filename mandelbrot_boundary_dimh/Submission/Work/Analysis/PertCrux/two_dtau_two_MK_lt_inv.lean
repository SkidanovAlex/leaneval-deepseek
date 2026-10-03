import Mathlib

namespace Work.Analysis.PertCrux

/-- For `x > 193` the polynomial `8800000 * x^3 + 2*x + 12` is bounded by `x^40`. -/
lemma poly_bound_of_gt_193 {x : ℝ} (hx : 193 < x) :
    8800000 * x ^ 3 + 2 * x + 12 < x ^ 40 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h4 : (8800015 : ℝ) ≤ x ^ 4 := by
    have h : (193 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) (le_of_lt hx) 4
    norm_num at h
    linarith
  have h37 : x ^ 4 ≤ x ^ 37 := pow_le_pow_right₀ hx1 (by norm_num)
  have h3 : (0 : ℝ) ≤ x ^ 3 := by positivity
  have hstep1 : x ^ 3 * x ^ 4 ≤ x ^ 3 * x ^ 37 := mul_le_mul_of_nonneg_left h37 h3
  have hstep2 : 8800015 * x ^ 3 ≤ x ^ 4 * x ^ 3 := mul_le_mul_of_nonneg_right h4 h3
  have hx3 : x ≤ x ^ 3 := by
    simpa using pow_le_pow_right₀ hx1 (by norm_num : (1 : ℕ) ≤ 3)
  have hkey : x ^ 40 = x ^ 3 * x ^ 37 := by rw [show (40 : ℕ) = 3 + 37 from rfl, pow_add]
  rw [hkey]
  nlinarith [hstep1, hstep2, hx3, hx, h3]

theorem two_dtau_two_MK_lt_inv {Ξ' MK dtau : ℝ} {α : ℂ} (hΞ' : 193 < Ξ')
    (hMKΞ : MK ≤ Ξ') (hdtau : dtau ≤ 4400000 * Ξ' ^ 3) (hinv : Ξ' ^ 40 ≤ 1 / ‖α‖) :
    2 * dtau + 2 * MK + 12 < 1 / ‖α‖ := by
  have hbig : 8800000 * Ξ' ^ 3 + 2 * Ξ' + 12 < Ξ' ^ 40 := poly_bound_of_gt_193 hΞ'
  have h1 : 2 * dtau + 2 * MK + 12 ≤ 8800000 * Ξ' ^ 3 + 2 * Ξ' + 12 := by
    nlinarith [hdtau, hMKΞ]
  linarith

end Work.Analysis.PertCrux

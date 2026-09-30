import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem log_norm_factor_ge {q : ℚ} {Θ : ℂ} {v : ℕ} {d σ : ℝ}
    (hqne : q ≠ 0) (hΘne : Θ ≠ 0)
    (hqd : Real.log ‖(q : ℂ)‖ ≥ -((v : ℝ) * Real.log 2 + Real.log σ + Real.log d))
    (hΘ : Real.log ‖Θ‖ ≥ -(d * σ + d * Real.log 2)) :
    Real.log ‖(q : ℂ) * (2 : ℂ) ^ v * Θ‖ ≥
      -(Real.log d + Real.log σ + d * σ + d * Real.log 2) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqne
  have hpow : (2 : ℂ) ^ v ≠ 0 := pow_ne_zero _ (by norm_num)
  have hA : ‖(q : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hqC
  have hB : ‖(2 : ℂ) ^ v‖ ≠ 0 := norm_ne_zero_iff.mpr hpow
  have hC : ‖Θ‖ ≠ 0 := norm_ne_zero_iff.mpr hΘne
  rw [norm_mul, norm_mul]
  rw [Real.log_mul (mul_ne_zero hA hB) hC, Real.log_mul hA hB]
  have hlog2 : Real.log ‖(2 : ℂ) ^ v‖ = (v : ℝ) * Real.log 2 := by
    rw [norm_pow, Real.log_pow]; norm_num
  rw [hlog2]
  linarith [hqd, hΘ]

end Work.BW

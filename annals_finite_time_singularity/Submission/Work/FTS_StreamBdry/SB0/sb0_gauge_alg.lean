import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB0

theorem sb0_gauge_alg {a ρ B θ κ Ainv : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hB : 0 < B) :
    ρ ^ 2 * Ainv * (κ * ((ρ ^ (3 * a) / B) ^ (-(3 / (3 * a))) / Real.cos θ))
      = κ * Ainv * B ^ (1 / a) / (ρ * Real.cos θ) := by
  -- `-(3/(3a)) = -(1/a)`, and `(ρ^(3a)/B)^(-(1/a)) = ρ^(-3)·B^(1/a)`.
  have hD : (ρ ^ (3 * a) / B) ^ (-(3 / (3 * a))) = ρ ^ (-3 : ℝ) * B ^ (1 / a) := by
    have h3 : (3 : ℝ) / (3 * a) = 1 / a := by field_simp
    have e1 : (3 : ℝ) * a * (-(1 / a)) = -3 := by field_simp
    have e2 : (-1 : ℝ) * (-(1 / a)) = 1 / a := by field_simp
    have h1 : ρ ^ (3 * a) / B = ρ ^ (3 * a) * B⁻¹ := by rw [div_eq_mul_inv]
    rw [h1, h3, Real.mul_rpow (Real.rpow_nonneg hρ.le _) (inv_nonneg.mpr hB.le)]
    rw [← Real.rpow_mul hρ.le (3 * a) (-(1 / a)), e1]
    rw [← Real.rpow_neg_one B]
    rw [← Real.rpow_mul hB.le (-1) (-(1 / a)), e2]
  -- the radial powers `ρ² · ρ^(-3) = ρ⁻¹`.
  have hρinv : ρ ^ (2 : ℕ) * ρ ^ (-3 : ℝ) = ρ⁻¹ := by
    have h2 := Real.rpow_add hρ (2 : ℝ) (-3)
    rw [show (2 : ℝ) + (-3) = (-1 : ℝ) by norm_num, Real.rpow_neg_one] at h2
    rw [Real.rpow_ofNat ρ 2] at h2
    exact h2.symm
  by_cases hc : Real.cos θ = 0
  · simp [hc]
  · have step2 : ρ ^ 2 * ((ρ ^ (3 * a) / B) ^ (-(3 / (3 * a)))) = B ^ (1 / a) * ρ⁻¹ := by
      rw [hD]
      rw [show ρ ^ 2 * (ρ ^ (-3 : ℝ) * B ^ (1 / a))
            = (ρ ^ 2 * ρ ^ (-3 : ℝ)) * B ^ (1 / a) by ring, hρinv]
      ring
    calc ρ ^ 2 * Ainv * (κ * ((ρ ^ (3 * a) / B) ^ (-(3 / (3 * a))) / Real.cos θ))
        = (ρ ^ 2 * ((ρ ^ (3 * a) / B) ^ (-(3 / (3 * a))))) * (Ainv * κ / Real.cos θ) := by
          ring
      _ = (B ^ (1 / a) * ρ⁻¹) * (Ainv * κ / Real.cos θ) := by rw [step2]
      _ = κ * Ainv * B ^ (1 / a) / (ρ * Real.cos θ) := by field_simp

end Work.FTS_StreamBdry.SB0

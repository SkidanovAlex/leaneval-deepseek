import Mathlib
import Submission.Work.CR.Flat.Cauchy.polarDz
import Submission.Work.CR.Flat.Cauchy.cauchyGreen_origin

open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- The radial part of the polar integrand integrates to zero over the disc
`(0,ρ) × (-π,π)`:

`∫_{(0,ρ)×(-π,π)} polZ1 F = (1/2) ∫_{-π}^{π} e^{-2iθ} (∫_0^ρ polA F (r,θ) dr) dθ
  = (1/2) ∫_{-π}^{π} e^{-2iθ} (-F 0) dθ = 0`,

since `∫_0^ρ polA F (r,θ) dr = -F 0` (`integral_deriv_rho`) and `∫_{-π}^{π} e^{-2iθ} dθ = 0`
(`integral_polarUnit_inv_sq`).  `polZ1` and the auxiliary lemmas are in
`Submission/Work/CR/Flat/Cauchy/polarDz.lean`. -/
theorem setIntegral_polZ1_zero {ρ : ℝ} (hρ : 0 < ρ) {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hsupp : Work.CR.Flat.SupportedInBall ρ F) :
    ∫ p in Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi,
        Work.CR.Flat.Cauchy.polZ1 F p
      ∂(MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.volume) = 0 := by
  -- Fubini: swap the order of integration (the swapped integrand is continuous on the box)
  have hswap : IntegrableOn (fun z : ℝ × ℝ => polZ1 F z.swap)
      (Ioo (-Real.pi) Real.pi ×ˢ Ioo (0 : ℝ) ρ) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ ℝ]
    exact integrableOn_Ioo_prod_of_continuous ((continuous_polZ1 hF).comp continuous_swap)
      (-Real.pi) Real.pi 0 ρ
  rw [setIntegral_prod_rev (s := Ioo (0 : ℝ) ρ) (t := Ioo (-Real.pi) Real.pi) hswap]
  -- the inner (`ρ`-)integral is independent of `θ` and equals `e^{-2iθ} (-F 0)`
  have hinner : ∀ θ : ℝ, ∫ r in Ioo (0 : ℝ) ρ, polZ1 F (r, θ)
      = ((1 / 2 : ℂ) * ((polarUnit θ)⁻¹ * (polarUnit θ)⁻¹)) * (-(F 0)) := by
    intro θ
    have hpt : ∀ r : ℝ, polZ1 F (r, θ)
        = ((1 / 2 : ℂ) * ((polarUnit θ)⁻¹ * (polarUnit θ)⁻¹)) * polA F (r, θ) := by
      intro r; simp only [polZ1]; ring
    rw [setIntegral_congr_fun measurableSet_Ioo (fun r _ => hpt r),
      MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc' Real.volume_singleton)]
    rw [← intervalIntegral.integral_of_le hρ.le]
    exact integral_deriv_rho hF hρ hsupp θ
  rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hinner θ)]
  -- the angular integral `∫ e^{-2iθ} dθ` vanishes
  have hzero : ∫ θ in Ioo (-Real.pi) Real.pi, (polarUnit θ)⁻¹ * (polarUnit θ)⁻¹ = 0 := by
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc' Real.volume_singleton)]
    rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    exact integral_polarUnit_inv_sq
  rw [show (fun θ : ℝ => ((1 / 2 : ℂ) * ((polarUnit θ)⁻¹ * (polarUnit θ)⁻¹)) * (-(F 0)))
      = fun θ : ℝ => ((polarUnit θ)⁻¹ * (polarUnit θ)⁻¹) * ((1 / 2 : ℂ) * (-(F 0))) by
    funext θ; ring]
  rw [MeasureTheory.integral_mul_const, hzero, zero_mul]

end Work.CR.Flat.Cauchy

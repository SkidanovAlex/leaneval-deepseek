import Mathlib

/-!
# Radial integration on `ℂ`

For `F : ℝ → ℝ`,
`∫ z : ℂ, F (‖z‖²) ∂volume = π ∫_{σ > 0} F σ ∂σ`
(area measure on `ℂ ≅ ℝ²`): the two-dimensional polar-coordinate formula for a radial integrand,
obtained from Mathlib's `Complex.integral_comp_polarCoord_symm` together with the substitution
`σ = r²`.  It is the source of the ubiquitous factor `2π` in Cauchy–Pompeiu theory.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- **Radial integration on `ℂ`.**  For `F : ℝ → ℝ`,
`∫ z, F (‖z‖^2) ∂volume = π ∫_{σ > 0} F σ ∂σ` (area measure on `ℂ ≅ ℝ²`).
This is the two-dimensional polar-coordinate formula in the special case of a radial integrand. -/
theorem integral_comp_normSq (F : ℝ → ℝ) :
    ∫ z : ℂ, F (‖z‖ ^ 2) ∂volume = Real.pi * ∫ σ in Set.Ioi 0, F σ := by
  rw [← Complex.integral_comp_polarCoord_symm (f := fun z : ℂ => F (‖z‖ ^ 2))]
  change (∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      p.1 • F (‖Complex.polarCoord.symm p‖ ^ 2)) = Real.pi * ∫ σ in Set.Ioi 0, F σ
  have hcongr : (∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • F (‖Complex.polarCoord.symm p‖ ^ 2))
      = ∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (fun r : ℝ => r * F (r ^ 2)) p.1 * (fun _ : ℝ => (1 : ℝ)) p.2 := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    rintro ⟨r, θ⟩ ⟨hr, _⟩
    show r • F (‖Complex.polarCoord.symm (r, θ)‖ ^ 2) = (r * F (r ^ 2)) * 1
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    simp [smul_eq_mul]
  rw [hcongr, Measure.volume_eq_prod]
  trans ((∫ r in Set.Ioi (0:ℝ), r * F (r ^ 2)) *
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ))
  · exact setIntegral_prod_mul (μ := volume) (ν := volume) (f := fun r : ℝ => r * F (r ^ 2))
      (g := fun _ : ℝ => (1 : ℝ)) (s := Set.Ioi (0:ℝ)) (t := Set.Ioo (-Real.pi) Real.pi)
  have htheta : ∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) = 2 * Real.pi := by
    rw [setIntegral_const, Measure.real_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hr : ∫ r in Set.Ioi (0:ℝ), r * F (r ^ 2) = (1 / 2) * ∫ σ in Set.Ioi (0:ℝ), F σ := by
    have h := integral_comp_rpow_Ioi F (p := 2) (by norm_num)
    have h2 : ∫ x in Set.Ioi (0:ℝ), 2 * (x * F (x ^ 2)) = ∫ y in Set.Ioi (0:ℝ), F y := by
      convert h using 2
      funext x
      simp only [smul_eq_mul]
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [integral_const_mul] at h2
    linarith
  rw [htheta, hr]
  ring

end Work.Analysis.Complex.DbarCauchy

end

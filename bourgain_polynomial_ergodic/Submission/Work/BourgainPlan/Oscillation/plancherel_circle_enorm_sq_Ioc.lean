import Submission.Commons.Analysis.Fourier.multiplier_square_function_l2

namespace Work.BourgainPlan.Oscillation

open MeasureTheory
open scoped ENNReal

/-- Plancherel for a bounded measurable circle multiplier on `(0,1]`, with the boundedness
hypothesis required only on the interval `(0,1]`. This is `Commons.Analysis.Fourier.
plancherel_circle_enorm_sq` with the (weaker, a.e.-sufficient) interval-localised bound on `m`. -/
theorem plancherel_circle_enorm_sq_Ioc (m g : ℝ → ℂ) (hm : Measurable m)
    (hmb : ∃ C : ℝ, ∀ θ, θ ∈ Set.Ioc (0:ℝ) 1 → ‖m θ‖ ≤ C)
    (hg : MemLp g 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    (∑' n : ℤ, ‖∫ θ in (0:ℝ)..1,
        m θ * g θ * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ)))‖ₑ ^ (2 : ℝ))
      = ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖m θ‖ ^ 2 * ‖g θ‖ ^ 2) := by
  have hab : (0:ℝ) < 1 := by norm_num
  obtain ⟨C, hC⟩ := hmb
  have hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), ‖m θ‖ ≤ C :=
    ae_restrict_of_forall_mem measurableSet_Ioc hC
  have hm_top : MemLp m ⊤ (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound (p := ⊤) hm.aestronglyMeasurable C hae
  have hhmg : MemLp (fun θ => m θ * g θ) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.ae_eq (ae_of_all _ fun θ => mul_comm (g θ) (m θ)) (hg.mul' hm_top)
  have hsumm : Summable (fun n : ℤ => ‖fourierCoeffOn hab (fun θ => m θ * g θ) n‖ ^ 2) :=
    (hasSum_sq_fourierCoeffOn hab hhmg).summable
  have hcongr : (∑' n : ℤ, ‖∫ θ in (0:ℝ)..1,
        m θ * g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ))
      = ∑' n : ℤ, ENNReal.ofReal (‖fourierCoeffOn hab (fun θ => m θ * g θ) n‖ ^ 2) := by
    refine tsum_congr (fun n => ?_)
    rw [Commons.Analysis.Fourier.enorm_complex_pow_two,
      Commons.Analysis.Fourier.intervalIntegral_char_eq_fourierCoeffOn]
  rw [hcongr, ← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsumm,
    (hasSum_sq_fourierCoeffOn hab hhmg).tsum_eq]
  congr 1
  rw [show ((1:ℝ) - 0)⁻¹ = 1 by norm_num, one_smul]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [norm_mul, mul_pow]

end Work.BourgainPlan.Oscillation

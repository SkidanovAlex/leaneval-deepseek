import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.LpSpace
import Submission.Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `L²` normalisation of the `p`-convention Fourier transform

`Submission.BoseGases.kinFT F p = ∫_y e^{−i⟪p,y⟫}F(y)dy = 𝓕 F ((2π)⁻¹ • p)` (the identity
`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`).  Consequently, for `F ∈ L¹ ∩ L²(ℝ³)`, the
*unnormalised* `p`-measure on the Fourier side carries the stray factor `(2π)³`:

`(2π)⁻³ ∫_p ‖kinFT F p‖² = ∫_x ‖F x‖²`,

which is Plancherel's theorem (`Lp.norm_fourier_eq` through
`Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2`) combined with the change of variables
`p = 2π ξ` (`Measure.integral_comp_inv_smul_of_nonneg`, Jacobian `(2π)^{finrank ℝ ℝ³} = (2π)³`).

This is the one-body/kinetic Plancherel identity used to pass between the `p`-space kinetic word
`kinPWord` and the position-space kinetic energy.
-/

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseKinLoc.Kinetic

/-- The squared modulus of the Fourier transform of an `L¹ ∩ L²` function is integrable: the
`L¹ ∩ L²` Plancherel transform is the `L²` Fourier transform, which is in `L²`. -/
theorem integrable_norm_fourier_sq {F : EuclideanSpace ℝ (Fin 3) → ℂ}
    (h1 : MeasureTheory.MemLp F 1 MeasureTheory.volume)
    (h2 : MeasureTheory.MemLp F 2 MeasureTheory.volume) :
    MeasureTheory.Integrable
      (fun ξ : EuclideanSpace ℝ (Fin 3) => ‖𝓕 F ξ‖ ^ 2) := by
  have hLp := Lp.memLp (𝓕 (MemLp.toLp F h2))
  have hae := Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral h1 h2
  exact (MeasureTheory.MemLp.ae_eq hae hLp).integrable_norm_pow (by norm_num)

/-- **Plancherel with the `p`-convention normalisation.** For `F ∈ L¹ ∩ L²(ℝ³)`, the function
`p ↦ ‖kinFT F p‖²` is integrable and `(2π)⁻³ ∫_p ‖kinFT F p‖² = ∫_x ‖F x‖²`. -/
theorem kinFT_sq_of_memLp {F : EuclideanSpace ℝ (Fin 3) → ℂ}
    (h1 : MeasureTheory.MemLp F 1 MeasureTheory.volume)
    (h2 : MeasureTheory.MemLp F 2 MeasureTheory.volume) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      ∧ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
            ‖Submission.BoseGases.kinFT F p‖ ^ 2)
          = ∫ x : EuclideanSpace ℝ (Fin 3), ‖F x‖ ^ 2 := by
  -- `kinFT F p = 𝓕 F ((2π)⁻¹ • p)`
  have hft : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinFT F p = 𝓕 F ((2 * Real.pi)⁻¹ • p) := fun p =>
    Work.SmallBoxBridge.Resolve.kinFT_eq_fourier F p
  have hpt : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Submission.BoseGases.kinFT F p‖ ^ 2 = ‖𝓕 F ((2 * Real.pi)⁻¹ • p)‖ ^ 2 :=
    fun p => by rw [hft p]
  -- integrability: rescale the integrable `‖𝓕 F ·‖²`
  have hInt2 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖𝓕 F ((2 * Real.pi)⁻¹ • p)‖ ^ 2) :=
    (integrable_norm_fourier_sq h1 h2).comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)
  refine ⟨hInt2.congr (Filter.Eventually.of_forall (fun p => (hpt p).symm)), ?_⟩
  -- the integral: substitute `p = 2π ξ`
  have hI1 : ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT F p‖ ^ 2
      = ∫ p : EuclideanSpace ℝ (Fin 3), ‖𝓕 F ((2 * Real.pi)⁻¹ • p)‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hI2 : ∫ p : EuclideanSpace ℝ (Fin 3), ‖𝓕 F ((2 * Real.pi)⁻¹ • p)‖ ^ 2
      = (2 * Real.pi) ^ 3 * ∫ ξ : EuclideanSpace ℝ (Fin 3), ‖𝓕 F ξ‖ ^ 2 := by
    have := Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (fun ξ : EuclideanSpace ℝ (Fin 3) => ‖𝓕 F ξ‖ ^ 2) (R := 2 * Real.pi) (by positivity)
    simpa [finrank_euclideanSpace_fin, smul_eq_mul] using this
  have hpl := Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2
    (memLp_one_iff_integrable.mp h1) h2
  rw [hI1, hI2, hpl, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (by positivity)), one_mul]

end Work.BoseKinLoc.Kinetic

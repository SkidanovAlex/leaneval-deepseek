import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.PortSmallB.gradNormSq_integral_eq_sum_fderivSq
import Submission.Work.BoseB1Cube.PortSmallB.kinFTEnergyIntegrableOne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kinetic energy of a `C¹` compactly supported function as an `ℝ≥0∞`-valued integral

For `u : ℝ³ → ℝ` of class `C¹` with compact support,

`∫⁻_p ‖p‖² ‖kinFT (u : ℂ) p‖² ≤ (2π)³ C` whenever `C ≥ ∫_z Σ_k (∂_k u z)²`.

The mathematical content is Plancherel for the `kinFT`-convention Fourier transform
(`Work.BoseFixB1S.gradient_plancherel_of_contDiff_one`)

`(2π)⁻³ ∫_p ‖p‖² ‖kinFT (u:ℂ) p‖² = ∫_z ‖∇u z‖²`,

together with the orthonormal-basis identity `‖∇u z‖² = Σ_k (∂_{e_k} u z)²`
(`Work.BoseB1Cube.PortSmallB.gradNormSq_integral_eq_sum_fderivSq`).

The passage from the Bochner integral to the `ℝ≥0∞`-valued (`lintegral`) form is
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`, which needs the integrability of the
Bochner integrand `p ↦ ‖p‖²‖kinFT (u:ℂ) p‖²`
(`Work.BoseB1Cube.PortSmallB.kinFTEnergyIntegrableOne`) and its positivity.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB1Cube.PortSmallB

/-- **Plancherel, in the form used by the port**: for `u : ℝ³ → ℝ` of class `C¹` with compact
support, the second moment of the `kinFT` transform equals `(2π)³` times the Dirichlet energy
written with the coordinate basis `kcStdBasis`. -/
theorem kinFT_sqMoment_eq_twoPiCubed_mul_sum_fderivSq
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) :
    (∫ p : EuclideanSpace ℝ (Fin 3),
        ‖p‖ ^ 2 *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (u z : ℂ)) p‖ ^ 2)
      = (2 * Real.pi) ^ 3 *
          ∫ z : EuclideanSpace ℝ (Fin 3),
            ∑ k : Fin 3, (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  have hp := Work.BoseFixB1S.gradient_plancherel_of_contDiff_one hu hcs
  rw [gradNormSq_integral_eq_sum_fderivSq u] at hp
  have hpi : (2 * Real.pi : ℝ) ^ 3 ≠ 0 := by positivity
  have h2 := congrArg (fun t : ℝ => (2 * Real.pi) ^ 3 * t) hp
  rw [← mul_assoc] at h2
  rwa [mul_inv_cancel₀ hpi, one_mul] at h2

theorem kinFTEnergyLintegralOne {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) {C : ℝ}
    (hC : (∫ z : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
        (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ C) :
    (∫⁻ p : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (‖p‖ ^ 2 *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (u z : ℂ)) p‖ ^ 2))
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) := by
  have hnn : 0 ≤ᵐ[volume] (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (u z : ℂ)) p‖ ^ 2) :=
    Filter.Eventually.of_forall fun p => by positivity
  have key := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (kinFTEnergyIntegrableOne hu hcs) hnn
  calc (∫⁻ p : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (‖p‖ ^ 2 *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (u z : ℂ)) p‖ ^ 2))
      = ENNReal.ofReal (∫ p : EuclideanSpace ℝ (Fin 3),
          ‖p‖ ^ 2 *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (u z : ℂ)) p‖ ^ 2) :=
        key.symm
    _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 *
          ∫ z : EuclideanSpace ℝ (Fin 3),
            ∑ k : Fin 3, (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
        rw [kinFT_sqMoment_eq_twoPiCubed_mul_sum_fderivSq hu hcs]
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hC (by positivity)

end Work.BoseB1Cube.PortSmallB

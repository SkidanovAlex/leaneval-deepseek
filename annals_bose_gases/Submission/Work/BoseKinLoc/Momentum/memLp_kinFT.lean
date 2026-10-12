import Mathlib.Analysis.Fourier.LpSpace
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.memLp_kinFT`

`kinFT F p = ∫_y e^{−i⟪p,y⟫}F(y)dy` is the corpus's `p`-convention Fourier transform, and
`kinFT F p = 𝓕 F ((2π)⁻¹ • p)` for Mathlib's `𝓕` (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`).
Hence for `F ∈ L¹ ∩ L²`:

* `kinFT F` is *continuous* (the Fourier integral of an `L¹` function, composed with the
  dilation `p ↦ (2π)⁻¹ • p`): `continuous_kinFT_of_integrable`;
* `kinFT F ∈ L²`: this is the L²-PLancherel content of `F ∈ L¹ ∩ L²`, obtained by identifying
  the pointwise Fourier integral with Mathlib's L² Fourier isometry
  (`Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral`) and using that integrability of
  the squared modulus is invariant under the dilation `p ↦ (2π)⁻¹ • p`
  (`MeasureTheory.Integrable.comp_smul` for a Haar measure).

The second point is `memLp_kinFT`, the lemma of this file; the objects `momForm`, `statU`,
`PsiC`, … of `momDefs` all live at this level of generality, so the statement is stated for an
arbitrary `F : ℝ³ → ℂ`.
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseKinLoc.Momentum

/-- The `p`-convention Fourier transform of an `L¹` function is continuous. -/
theorem continuous_kinFT_of_integrable {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : MeasureTheory.Integrable u) : Continuous (Submission.BoseGases.kinFT u) := by
  -- `kinFT u` is Mathlib's Fourier integral `𝓕 u` composed with the dilation `p ↦ (2π)⁻¹ • p`.
  rw [show Submission.BoseGases.kinFT u
      = fun p : EuclideanSpace ℝ (Fin 3) =>
          FourierTransform.fourier u ((2 * Real.pi)⁻¹ • p)
      from funext fun p => Work.SmallBoxBridge.Resolve.kinFT_eq_fourier u p]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hu).comp (continuous_const_smul _)

theorem memLp_kinFT {F : EuclideanSpace ℝ (Fin 3) → ℂ} (h1 : MeasureTheory.Integrable F) (h2 : MeasureTheory.MemLp F 2 MeasureTheory.volume) : MeasureTheory.MemLp (Submission.BoseGases.kinFT F) 2 MeasureTheory.volume := by
  have hF1 : MeasureTheory.MemLp F 1 MeasureTheory.volume :=
    MeasureTheory.memLp_one_iff_integrable.mpr h1
  -- (1) Mathlib's L² Fourier isometry: `𝓕 F ∈ L²`, and its pointwise value is the Fourier
  -- integral of `F`.
  have hFfour : MeasureTheory.MemLp
      (fun ξ : EuclideanSpace ℝ (Fin 3) => FourierTransform.fourier F ξ) 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    (MeasureTheory.memLp_congr_ae
      (Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral hF1 h2)).mp
      (MeasureTheory.Lp.memLp
        (FourierTransform.fourier (h2.toLp F) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))))
  -- (2) Integrability of the squared modulus of `𝓕 F`.
  have hIntξ : MeasureTheory.Integrable
      (fun ξ : EuclideanSpace ℝ (Fin 3) => ‖FourierTransform.fourier F ξ‖ ^ 2) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hFfour.aestronglyMeasurable).mp hFfour
  -- (3) Integrability survives the dilation `p ↦ (2π)⁻¹ • p` (Lebesgue measure is a Haar
  -- measure, so the dilation only changes the value of the integral by a constant).
  have hIntp : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) =>
        ‖FourierTransform.fourier F ((2 * Real.pi)⁻¹ • p)‖ ^ 2) :=
    hIntξ.comp_smul (by positivity : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0)
  -- (4) Transfer to `kinFT F` (equality of the integrands, pointwise).
  have hEq : (fun p : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      = fun p : EuclideanSpace ℝ (Fin 3) =>
          ‖FourierTransform.fourier F ((2 * Real.pi)⁻¹ • p)‖ ^ 2 :=
    funext fun p => by rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  have hint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT F p‖ ^ 2) :=
    hEq ▸ hIntp
  -- (5) `kinFT F` is continuous, hence AEStronglyMeasurable, and its square is integrable.
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (continuous_kinFT_of_integrable h1).aestronglyMeasurable).mpr hint

end Work.BoseKinLoc.Momentum

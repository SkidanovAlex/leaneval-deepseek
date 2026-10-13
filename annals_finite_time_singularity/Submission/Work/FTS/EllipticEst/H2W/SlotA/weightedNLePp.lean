import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.SlotA

/-- Monotonicity of the `z`-integral against the radial weight `w2`, for two `z`-dependent
quantities `N`, `M` that are pointwise (a.e.) comparable with the constant `(1+η)^{-2}`.

This is the `z`-integration step of the sharp Hardy bound
`N ≤ (1+η)^{-2} Pp`: the slicewise inequality `N z ≤ (1+η)^{-2} M z` holds almost everywhere in
`z`, and `w2 ≥ 0`, so the two `${z}`-integrals inherit it. -/
private theorem integral_w2_mul_le_of_ae_slice {η : ℝ} {N M : ℝ → ℝ}
    (hNi : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.EllipticEst.AngSecond.w2 z * N z) Work.Spaces.Iz)
    (hMi : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.EllipticEst.AngSecond.w2 z * M z) Work.Spaces.Iz)
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      N z ≤ (1 / (1 + η) ^ 2) * M z) :
    (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.w2 z * N z)
      ≤ (1 / (1 + η) ^ 2)
          * (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.w2 z * M z) := by
  have hNi' : MeasureTheory.Integrable (fun z => Work.FTS.EllipticEst.AngSecond.w2 z * N z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hNi
  have hMi' : MeasureTheory.Integrable (fun z => Work.FTS.EllipticEst.AngSecond.w2 z * M z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hMi
  have hle : (fun z => Work.FTS.EllipticEst.AngSecond.w2 z * N z)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (1 / (1 + η) ^ 2) * (Work.FTS.EllipticEst.AngSecond.w2 z * M z)) := by
    filter_upwards [h] with z hz
    calc Work.FTS.EllipticEst.AngSecond.w2 z * N z
        ≤ Work.FTS.EllipticEst.AngSecond.w2 z * ((1 / (1 + η) ^ 2) * M z) :=
          mul_le_mul_of_nonneg_left hz (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
      _ = (1 / (1 + η) ^ 2) * (Work.FTS.EllipticEst.AngSecond.w2 z * M z) := by ring
  have h2 := MeasureTheory.integral_mono_ae hNi' (hMi'.const_mul _) hle
  rwa [MeasureTheory.integral_const_mul] at h2

theorem weightedNLePp (η : ℝ) (U V : ℝ → ℝ → ℝ)
    (hNint : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.AngSecond.w2 z
        * ∫ θ in Work.Spaces.Iθ, (U z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-2 - η)) Work.Spaces.Iz)
    (hHint : ∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => (U z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-2 - η)) Work.Spaces.Iθ)
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, (U z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-2 - η))
          ≤ (1 / (1 + η) ^ 2) * (∫ θ in Work.Spaces.Iθ, (V z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-η)))
    (hVint : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.AngSecond.w2 z
        * ∫ θ in Work.Spaces.Iθ, (V z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.w2 z
        * ∫ θ in Work.Spaces.Iθ, (U z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-2 - η))
      ≤ (1 / (1 + η) ^ 2)
          * (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.w2 z
              * ∫ θ in Work.Spaces.Iθ, (V z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) :=
  integral_w2_mul_le_of_ae_slice hNint hVint hsl

end Work.FTS.EllipticEst.H2W.SlotA

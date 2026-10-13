import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Alpha4

/-- **Monotonicity of the weighted `z`-integral.**  A pointwise inequality of the form
`κ (γ A) ≤ -(γ B) + c₁ (γ C)` on the half-line `Iz = [0,∞)` upgrades to the same
inequality for the integrals, provided the three weighted functions are integrable
against `volume.restrict Iz`.  Nothing about `γ` is used: the content is that
`MeasureTheory.integral_mono_ae` may be applied to the a.e. inequality that
`MeasureTheory.ae_restrict_of_forall_mem` produces from `hpt`, together with the
linearity of the Bochner integral (which needs the integrability hypotheses). -/
theorem weighted_slice_mono {κ c₁ : ℝ} {γ A B C : ℝ → ℝ}
    (hpt : ∀ z ∈ Work.Spaces.Iz,
      κ * (γ z * A z) ≤ -(γ z * B z) + c₁ * (γ z * C z))
    (hA : MeasureTheory.Integrable (fun z => γ z * A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hB : MeasureTheory.Integrable (fun z => γ z * B z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hC : MeasureTheory.Integrable (fun z => γ z * C z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    κ * (∫ z in Work.Spaces.Iz, γ z * A z)
      ≤ -(∫ z in Work.Spaces.Iz, γ z * B z)
        + c₁ * (∫ z in Work.Spaces.Iz, γ z * C z) := by
  -- The pointwise hypothesis is an a.e. inequality for the restricted measure.
  have hae : (fun z => κ * (γ z * A z))
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => -(γ z * B z) + c₁ * (γ z * C z)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt
  -- Integrability of the two sides of that inequality.
  have h1 : MeasureTheory.Integrable (fun z => κ * (γ z * A z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hA.const_mul κ
  have hB' : MeasureTheory.Integrable (fun z => -(γ z * B z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hB.neg
  have hC' : MeasureTheory.Integrable (fun z => c₁ * (γ z * C z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hC.const_mul c₁
  have h2 : MeasureTheory.Integrable
      (fun z => -(γ z * B z) + c₁ * (γ z * C z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hB'.add hC'
  have h := MeasureTheory.integral_mono_ae h1 h2 hae
  -- Push the constants and the sign through the integral on both sides.
  rw [MeasureTheory.integral_const_mul κ (fun z => γ z * A z),
      MeasureTheory.integral_add hB' hC', MeasureTheory.integral_neg,
      MeasureTheory.integral_const_mul] at h
  exact h

end Work.FTS.EllipticEst.Alpha4

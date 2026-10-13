import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

theorem lintegralConv (W : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (hW : ∀ z, 0 ≤ W z)
    (hf : ∀ z θ, 0 ≤ f z θ)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ)
    (hout : MeasureTheory.IntegrableOn
      (fun z => W z * (∫ θ in Work.Spaces.Iθ, f z θ)) Work.Spaces.Iz) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (W z)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f z θ)))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, W z * (∫ θ in Work.Spaces.Iθ, f z θ)) := by
  -- For almost every `z`, the lintegral of `ofReal ∘ f z ·` equals `ofReal` of the integral.
  have hsl' : (fun z => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, f z θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f z θ)) :=
    hslice.mono fun z hz =>
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hz
        (Filter.Eventually.of_forall fun θ => hf z θ)
  have h1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (W z)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f z θ)))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (W z)
        * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, f z θ) :=
    MeasureTheory.lintegral_congr_ae (hsl'.symm.mono fun z hz =>
      congrArg (fun t => ENNReal.ofReal (W z) * t) hz)
  have h2 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (W z)
        * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, f z θ))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (W z * ∫ θ in Work.Spaces.Iθ, f z θ) :=
    MeasureTheory.lintegral_congr fun z => (ENNReal.ofReal_mul (hW z)).symm
  rw [h1, h2]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hout
    (Filter.Eventually.of_forall fun z => mul_nonneg (hW z)
      (MeasureTheory.integral_nonneg fun θ => hf z θ))).symm

end Work.FTS.EllipticEst.Prop.CutEnergyAux

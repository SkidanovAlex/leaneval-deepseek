import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.AuxAngRad

/-- The light angular weight `σ = sin(2θ)^{-η}` is integrable on the closed angular interval
`Iθ` (the exponent `η = 99/100` lies in `(0,1)`). -/
theorem integrableOn_smE :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ)
      Work.Spaces.Iθ := by
  simpa only [Work.FTS.Nonlinear.RadialProd.smE] using
    (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta Work.Spaces.eta_pos
      Work.Spaces.eta_lt_one).1

theorem angRad_majorant_integrable {α : ℝ} {r G : ℝ → ℝ} {B0 B1 : ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z)) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
        Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.Nonlinear.RadialProd.Rint r z
            * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
                + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
        Work.Spaces.Iz := by
  -- the angular majorant is integrable: it is a combination of the integrable `σ = smE`
  -- and the (hypothesised integrable) `G² · smG α`.
  have h2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
      Work.Spaces.Iθ := hGint.const_mul _
  have h2' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      Work.Spaces.Iθ :=
    h2.congr_fun (fun θ _ => by ring) measurableSet_Icc
  have hg : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      Work.Spaces.Iθ := (integrableOn_smE.const_mul _).add h2'
  refine ⟨fun z _ => ?_, ?_⟩
  · -- the `θ`-integrand is a constant (`Rint r z`) multiple of the angular majorant
    exact hg.const_mul (Work.FTS.Nonlinear.RadialProd.Rint r z)
  · -- `∫_θ Rint r z · (…) = Rint r z · ∫_θ (…)`, and `Rint r` is integrable for an `ℋ⁴`
    -- radial datum
    have hRint := Work.FTS.NonlinRows.AuxAngRad.integrableOn_Rint_of_HkMem hrmem
    have hK : MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.FTS.Nonlinear.RadialProd.Rint r z
          * (∫ θ in Work.Spaces.Iθ,
              (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
                + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)))
        Work.Spaces.Iz := hRint.mul_const _
    refine hK.congr_fun (fun z _ => ?_) measurableSet_Ici
    rw [MeasureTheory.integral_const_mul]

end Work.FTS.NonlinRows.AuxAngRad

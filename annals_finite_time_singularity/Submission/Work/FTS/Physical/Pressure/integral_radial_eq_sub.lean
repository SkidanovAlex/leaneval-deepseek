import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.Pressure

theorem integral_radial_eq_sub {F : Work.FTS.Physical.R3 → Work.FTS.Physical.R3}
    {P : Work.FTS.Physical.R3 → ℝ} (hF : Continuous F)
    (hP : ∀ z, HasFDerivAt P (innerSL ℝ (F z)) z) (y : Work.FTS.Physical.R3) :
    ∫ s in (0 : ℝ)..1, inner ℝ (F (s • y)) y = P y - P 0 := by
  -- The fundamental theorem of calculus applied to the ray `s ↦ s • y`:
  -- `d/ds P (s • y) = ⟪F (s • y), y⟫` by the chain rule and `∇P = F`.
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => P (s • y)) ((innerSL ℝ (F (s • y))) y) s := by
    intro s _
    have hc : HasDerivAt (fun s : ℝ => s • y) y s := by
      simpa using (hasDerivAt_id s).smul_const y
    exact (hP (s • y)).comp_hasDerivAt s hc
  have hcont : Continuous (fun s : ℝ => (innerSL ℝ (F (s • y))) y) := by
    rw [show (fun s : ℝ => (innerSL ℝ (F (s • y))) y)
          = fun s => inner ℝ (F (s • y)) y from by
        funext s; exact innerSL_apply_apply ℝ _ _]
    exact (hF.comp (continuous_id.smul continuous_const)).inner continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)
  simpa [innerSL_apply_apply] using h

end Work.FTS.Physical.Pressure

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.H1IP_isHkIP
import Submission.Work.FTS.CoercivityStep.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityStep.Base

open MeasureTheory

/-- The weighted pairing `wip ρ A B = ∫∫ A·B·ρ` is symmetric in its two function
arguments: the integrand `A z θ * B z θ * ρ z θ` is commutative in `A` and `B`. -/
theorem wip_comm (ρ A B : ℝ → ℝ → ℝ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ B A := by
  unfold Work.Coercivity.wip
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  ring

/-- The `ℋ¹` inner product is symmetric, with no hypotheses on the profiles. -/
theorem H1IP_comm (α : ℝ) (f g : ℝ → ℝ → ℝ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α g f := by
  rw [Work.Coercivity.H1IP, Work.Coercivity.H1IP]
  rw [wip_comm (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz f) (Work.Spaces.Dz g),
      wip_comm (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f g,
      wip_comm (fun z _ => Work.Spaces.w z ^ 2) f g,
      wip_comm (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth f) (Work.Spaces.Dth g)]

theorem H1IP_add_snd (α : ℝ) (f g₁ g₂ : ℝ → ℝ → ℝ)
    (hf : Work.FTS.CoercivityStep.HkReg α 1 f)
    (h₁ : Work.FTS.CoercivityStep.HkReg α 1 g₁)
    (h₂ : Work.FTS.CoercivityStep.HkReg α 1 g₂)
    (h₁₂ : Work.FTS.CoercivityStep.HkReg α 1 (g₁ + g₂)) :
    Work.Coercivity.H1IP α f (g₁ + g₂)
      = Work.Coercivity.H1IP α f g₁ + Work.Coercivity.H1IP α f g₂ := by
  rw [H1IP_comm α f (g₁ + g₂),
    Work.Coercivity.H1IP_add_eq α g₁ g₂ f h₁.1 h₂.1 hf.1 h₁.2 h₂.2 hf.2,
    H1IP_comm α g₁ f, H1IP_comm α g₂ f]

end Work.FTS.CoercivityStep.Base

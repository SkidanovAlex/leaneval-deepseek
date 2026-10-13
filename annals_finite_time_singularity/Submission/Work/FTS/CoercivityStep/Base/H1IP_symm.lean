import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.FTS.CoercivityStep.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Base

/-! ## A helper: `wip` is symmetric in its two function arguments

`wip ρ A B = ∫_z ∫_θ A(z,θ) * B(z,θ) * ρ(z,θ)` is a *set integral* (over `Iz × Iθ`):
the two slices are integrals over the sets `Iz = [0,∞)` and `Iθ = [0,π/2]`, so the
pointwise identity `(A*B)*ρ = (B*A)*ρ` has to be pushed through the two nested set
integrals with `setIntegral_congr_fun` (no integrability is needed — both sides are
the same integral of equal integrands, including the junk-value case). -/

theorem wip_comm (ρ A B : ℝ → ℝ → ℝ) : Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ B A := by
  unfold Work.Coercivity.wip
  refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iz) measurableSet_Ici
    (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
    (fun θ _ => ?_)
  ring

/-- `H1IP α` is symmetric: it is the sum of four pairings `wip ρ (D f) (D g)` with
positive weights, each of which is symmetric by `wip_comm`. -/
theorem H1IP_symm (α : ℝ) (f g : ℝ → ℝ → ℝ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α g f := by
  unfold Work.Coercivity.H1IP
  rw [wip_comm (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz f) (Work.Spaces.Dz g),
      wip_comm (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f g,
      wip_comm (fun z _ => Work.Spaces.w z ^ 2) f g,
      wip_comm (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))
        (Work.Spaces.Dth f) (Work.Spaces.Dth g)]

end Work.FTS.CoercivityStep.Base

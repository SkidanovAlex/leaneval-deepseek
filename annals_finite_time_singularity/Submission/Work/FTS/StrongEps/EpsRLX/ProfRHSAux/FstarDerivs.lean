import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open scoped Real Topology
open Filter

theorem FstarDerivs (α : ℝ) (z θ : ℝ) :
    Work.Construction.Fstar α z θ = Work.Spaces.Gam α θ * (α * Work.FM.Fstar z / Work.Spaces.c α) ∧
    Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = Work.Spaces.Gam α θ * (α * (z * deriv Work.FM.Fstar z) / Work.Spaces.c α) ∧
    Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = (α * Work.FM.Fstar z / Work.Spaces.c α)
          * (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Work.Construction.Fstar; ring
  · unfold Work.Spaces.Dz Work.Spaces.pz Work.Construction.Fstar
    rw [deriv_const_mul_field]
    ring
  · unfold Work.Spaces.Dth Work.Spaces.pth Work.Construction.Fstar
    have hfun : (fun θ' => α * (Work.Spaces.Gam α θ' / Work.Spaces.c α) * Work.FM.Fstar z)
        = (fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ') := by
      funext θ'; ring
    rw [hfun, deriv_const_mul_field]
    ring

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux

import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.EllipticEst.remov.AeChainDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `remov/AeI1PaperDefs` — the *decoupled* paper-shaped `I₁` interface

`remov.AeI1LowerPos` (in `remov/AeChainDefs.lean`) states the `I₁` lower bound with
`‖G‖_ρ`-errors, so its proof needs Step 1's radial bound `α‖z∂_zu‖_ρ ≤ C‖G‖_ρ`.  The
paper's computation (the `z`- and `θ`-integrations by parts plus the sharp Hardy inequality)
produces instead the *`⟨z∂_zu, z∂_zu⟩`-form* collected here as `AeI1Paper`, which is
Step-1-free; the conversion to `AeI1LowerPos` is the pure arithmetic
`remov.AeI1LowerPos_of_paper` in `remov/AeStep2Holds.lean`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- **The paper-shaped `I₁` lower bound in the class `AeData`** (the *decoupled* form of
`AeI1LowerPos`): the positive term is kept and the errors are written with `⟨z∂_zu, z∂_zu⟩`,
`√⟨z∂_zu, z∂_zu⟩·√⟨∂_θθu, ∂_θθu⟩` instead of the source norms `‖G‖_ρ`, `‖B‖_ρ`.  This is what
the paper's computation (the `z`- and `θ`-integrations by parts plus the sharp Hardy inequality)
yields directly; the conversion to `AeI1LowerPos` is then pure Step-1 arithmetic — see
`AeI1LowerPos_of_paper` below. -/
def AeI1Paper : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
          (α ^ 2 * Work.Spaces.HkSq α 0
            (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)))
        - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                  (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
        ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u)


end Work.FTS.EllipticEst.remov

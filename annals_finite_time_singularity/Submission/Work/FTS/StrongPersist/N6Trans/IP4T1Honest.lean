import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.IP4T1Aux
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.LeafSum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open scoped Real Topology

/-- **The level-4 `T1` transport clause in the honest class** (`SmoothOpen` + `HkMem α 4`, with
`DecayAll 4 g` and no `HkMem α 5 g`).

It is the combination of the slot domination `IP4_le_leafSum` (with constant `3^3·10^22`) and
the honest-class `leafSum` bound `T1Hon.leafSum_bound` for the `D_θ`-transport pairing, via
`IP4T1Honest_of_leafSumBound`. -/
theorem IP4T1Honest : ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
        Work.Spaces.DecayAll 4 g →
      |Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α
          (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
        ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
            * (Work.Spaces.HkNorm α 4 g) ^ 2 :=
  IP4T1Honest_of_leafSumBound T1Hon.leafSum_bound

end Work.FTS.StrongPersist.N6Trans

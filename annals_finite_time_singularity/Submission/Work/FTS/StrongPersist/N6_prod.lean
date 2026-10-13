import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.ClauseFields
import Submission.Work.FTS.StrongPersist.N6.Prod6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

theorem N6_prod : ∃ Xi Cpow α₂ : ℝ, 0 < Xi ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 g →
      Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.StrongPersist.Xn6 α (fun z θ => f z θ * g z θ)
        ≤ Xi * α ^ (-Cpow) * Work.FTS.StrongPersist.Xn6 α f
          * Work.FTS.StrongPersist.Xn6 α g := by
  exact Work.FTS.StrongPersist.N6.prod_field6

end Work.FTS.StrongPersist

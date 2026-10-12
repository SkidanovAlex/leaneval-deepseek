import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

theorem a0d_comp_a0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    (Work.BoseB4.a0d : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E).comp Work.BoseB4.a0
      = Work.BoseB4.a0.comp Work.BoseB4.a0d
        - (1 : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E) := by
  -- This is the canonical commutation relation `[a₀, a₀†] = 1` (`Defs.ccr`),
  -- `a0 ∘ a0d = a0d ∘ a0 + 1`, solved for `a0d ∘ a0`.
  have h := ccr (E := E)
  rw [h]
  abel

end Work.BoseB4

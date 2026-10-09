import Mathlib
import Submission.NK.LocalStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalStructure.Brauer

open scoped Classical Pointwise

universe u

theorem localDecompositionCriterion_of_brauer_and_finishing
    {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ'] {p : ℕ}
    (hBr : NK.LocalStructure.LocalBrauerLocalisation p K K' κ κ')
    (hFin : NK.LocalStructure.LocalFinishingStep p K K' κ κ') :
    NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ' := by
  intro H hHclosed hHnorm hκ A x hx
  rcases hBr.exists_stabilizer H hHclosed hκ A x hx with ⟨A₀, hA₀, hHle, hHrel⟩
  exact hFin H hHclosed hHnorm hκ A₀ hA₀ hHle hHrel

end NK.LocalStructure.Brauer

import Submission.Blueprint.Interfaces
import Submission.Work.Models.Abstract.ModelData
import Submission.Work.Models.Abstract.modelFactsFor
import Submission.Work.Models.Abstract.modelData_mapEquiv
import Submission.Work.Models.ModelData.szModelData
import Submission.Work.Models.ModelData.pSL2ModelData
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.Models.Port.BenderBasic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.models` — the `Models` area theorem

`ModelFactsProp` follows from the three model families: each carries a `ModelData`
(a `BenderPair` plus the model facts `K₀ = J(T,w)` cyclic of order `#Inv(B) ≥ 2`, `T` abelian,
`w² = 1`, involutions of `U` central in `U`), the model data transports along a group
isomorphism, and `ModelData.modelFactsFor` turns it into the body of `ModelFactsProp`.
-/

set_option autoImplicit false
open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.Models

/-- **`ModelFactsProp`** (`Submission.Blueprint.ModelFactsProp`) for the three model families. -/
theorem models_prop : ModelFactsProp :=
  modelFactsProp_of fun Y _ _ hY => by
    have hs : IsSimpleGroup Y := Submission.isSimpleGroup_of_isSimpleBenderGroup hY
    cases hY with
    | isPSL2 n hn e =>
      obtain ⟨P⟩ := ModelData.pSL2ModelData n hn
      obtain ⟨P'⟩ := Abstract.modelData_mapEquiv P e.symm
      exact Abstract.modelFactsFor P' hs
    | isSuzuki n hn e =>
      obtain ⟨P⟩ := ModelData.szModelData n hn
      obtain ⟨P'⟩ := Abstract.modelData_mapEquiv P e.symm
      exact Abstract.modelFactsFor P' hs
    | isPSU3 n hn e =>
      obtain ⟨P⟩ := ModelData.psu3ModelData_data n hn
      obtain ⟨P'⟩ := Abstract.modelData_mapEquiv P e.symm
      exact Abstract.modelFactsFor P' hs

/-- The area theorem in the shape used by `Submission/Blueprint/Assembly.lean`
(each area theorem may assume `FeitThompsonProp`). -/
theorem models (hFT : FeitThompsonProp) : ModelFactsProp := models_prop

end Work.Models

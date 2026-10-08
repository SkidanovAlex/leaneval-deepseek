import Submission.Work.ThmG2.Main
import Submission.Work.ThmG2.IndTwoV2Proof

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThmG2`: assembly of Théorème G from the seven external inputs

The corrected statement of Théorème G, with every structural input named.  Import
`Submission.Work.ThmG2.All` and use:

```lean
theorem myUse : ThmGProp :=
  Work.ThmG2.thmG2_of_seven hFT hFS hC4 hTh kNeOneProp coprimeDQProp fpfOddPartProp
    existsLinearV2Prop indTwoV2Prop degreeProp vanishesOffProp
```

(or `Work.ThmG2.thmG2 hFT hFS hC4 hTh hStr` for a caller who already has
`RankOneStructure2Prop`).

Owners of the external inputs:

* `KNeOneProp` — area `ThreePoints`;
* `CoprimeDQProp` — area `DoubleTransitivity`;
* `FpfOddPartProp`, `ExistsLinearV2Prop` (`Work.ThmF.ChV12.exists_linear_v2`) and `IndTwoV2Prop`
  (`Work.ThmF.ChV12.ind_two_v2`) — area `ThmF`;
* `DegreeProp`, `VanishesOffProp` — area `FeitSibley`.

`DNeBotProp` (field 2) is **not** an input: it is discharged by `Work.ThmG.dNeBotProp`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical
open Submission.Blueprint

namespace Work.ThmG2

open Work.ThmG

/-- **Théorème G** (corrected inputs) from the seven external inputs: the four area `Prop`s
`FeitThompsonProp`, `FeitSibleyProp`, `ChIIFourProp`, `ThompsonFrobeniusProp`, plus the seven
structural inputs of `RankOneStructure2` with `D ≠ 1` discharged internally. -/
theorem thmG2_of_seven (hFT : FeitThompsonProp) (hFS : FeitSibleyProp) (hC4 : ChIIFourProp)
    (hTh : ThompsonFrobeniusProp) (h1 : KNeOneProp) (h3 : CoprimeDQProp) (h4 : FpfOddPartProp)
    (h5 : ExistsLinearV2Prop) (h6 : IndTwoV2Prop) (h7 : DegreeProp) (h8 : VanishesOffProp) :
    ThmGProp :=
  thmG2 hFT hFS hC4 hTh (rankOneStructure2_of h1 h3 h4 h5 h6 h7 h8)

/-- **Théorème G** (corrected inputs) from the seven external inputs, bundling the two
`FeitSibley` inputs (`DegreeProp`, `VanishesOffProp`): six arguments. -/
theorem thmG2_of_six (hFT : FeitThompsonProp) (hFS : FeitSibleyProp) (hC4 : ChIIFourProp)
    (hTh : ThompsonFrobeniusProp) (h1 : KNeOneProp) (h3 : CoprimeDQProp) (h4 : FpfOddPartProp)
    (h5 : ExistsLinearV2Prop) (h6 : IndTwoV2Prop) (h78 : DegreeProp ∧ VanishesOffProp) :
    ThmGProp :=
  thmG2_of_seven hFT hFS hC4 hTh h1 h3 h4 h5 h6 h78.1 h78.2

/-- **Théorème G** (corrected inputs) with field 6 discharged inside this area: six external
inputs (`FeitThompsonProp`, `FeitSibleyProp`, `ChIIFourProp`, `ThompsonFrobeniusProp` and the
fields 1, 3, 4, 5, 7, 8) and `Work.ThmG2.indTwoV2Prop` for field 6. -/
theorem thmG2_of_rankOneStructure2_of_seven (hFT : FeitThompsonProp) (hFS : FeitSibleyProp)
    (hC4 : ChIIFourProp) (hTh : ThompsonFrobeniusProp) (h1 : KNeOneProp) (h3 : CoprimeDQProp)
    (h4 : FpfOddPartProp) (h5 : ExistsLinearV2Prop) (h7 : DegreeProp) (h8 : VanishesOffProp) :
    ThmGProp :=
  thmG2_of_seven hFT hFS hC4 hTh h1 h3 h4 h5 indTwoV2Prop h7 h8

end Work.ThmG2

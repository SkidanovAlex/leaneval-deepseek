import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.BSHallW.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.OddChain.ChV3PropOdd` — the §3 contradiction with the corrected Hall–Wielandt input

This is `Work.ThmF.ChV3.ChV3Prop` (`Submission/Work/ThmF/ChV3/Chain.lean`) with
`Work.ThmF.HallWielandtProp` replaced by `Work.BSHallW.HallWielandtOddProp`: the four literature
inputs threaded through the chain are Wielandt's fixed-point formula, the **corrected** (D2:
`p ≠ 2`) Hall–Wielandt transfer theorem, HB IX (2-7), and the near-field shadow of App. XI.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BSHallW.OddChain

open Submission.Blueprint
open Work.ThmF.ChV3

/-- **Ch. V §3 with the corrected Hall–Wielandt input**: the context `CtxF H Q t s r P` is
contradictory (steps (1)–(17) of Peterfalvi II pp. 248–256), given the other areas' `Prop`s used by
§1–§2 and the four literature inputs §3 quotes, with `p ≠ 2` built into the Hall–Wielandt input. -/
def ChV3PropOdd : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G},
    FeitThompsonProp → ChIIFourProp → ThompsonFrobeniusProp →
    Work.ThmF.WielandtFixedPoint → Work.BSHallW.HallWielandtOddProp →
    Work.ThmF.ArithmeticNineTwoSeven → NearFieldAppXIProp →
    CtxF H Q t s r P → False

end Work.BSHallW.OddChain

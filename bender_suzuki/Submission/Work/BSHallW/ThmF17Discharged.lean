import Submission.Work.BSHallW.Main
import Submission.Work.BSHallW.OddChain.ThmF17Odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.ThmF17Discharged` — the live Théorème F with the D2 defect removed

`Work.ThmF17.ThmF17` (`Submission/Work/ThmF17/ThmF17.lean`, the current form of Théorème F: the
§3 chain with the input `NearFieldExpProp` no longer assumed) still takes the **false at `p = 2`**
input `hHW : Work.ThmF.HallWielandtProp`.

`Work.BSHallW.ThmF17Odd` re-assembles that theorem with `Work.BSHallW.HallWielandtOddProp` in its
place (same chain, run in `Submission/Work/BSHallW/OddChain/`); the present module discharges the
corrected input with the proved `Work.BSHallW.hallWielandtOdd`, giving Théorème F with the audit
defect **D2** removed and no Hall–Wielandt hypothesis at all.

Summary of what the caller gets:

* `Work.BSHallW.ThmF16Odd` — `Work.ThmF.ThmF16` with `hHW : HallWielandtOddProp`;
* `Work.BSHallW.thmF16'` — the same, `hHW` discharged;
* `Work.BSHallW.ThmF17Odd` — `Work.ThmF17.ThmF17` with `hHW : HallWielandtOddProp`;
* `Work.BSHallW.thmF17'` — the same, `hHW` discharged (this one is the current path).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.BSHallW

/-- **Théorème F (the `ThmF17` form) with the D2 defect removed**: `Work.ThmF17.ThmF17` with the
(false at `p = 2`) Hall–Wielandt input discharged by the proved `Work.BSHallW.hallWielandtOdd`. -/
theorem thmF17' (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hTh : ThompsonFrobeniusProp)
    (hW : Work.ThmF.WielandtFixedPoint) (hA : Work.ThmF.ArithmeticNineTwoSeven)
    (hNF : Work.ThmF.ChV3.NearFieldAppXIProp) (hXI2 : Work.ThmF.ChV3.AppXIProp2)
    (hNFF : Work.ThmF.ChV3.NearFieldFieldProp) (hHig : HigmanProp) : ThmFProp :=
  ThmF17Odd hFT hC4 hTh hW hallWielandtOdd hA hNF hXI2 hNFF hHig

end Work.BSHallW

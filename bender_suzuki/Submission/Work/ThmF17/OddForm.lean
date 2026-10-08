import Submission.Work.ThmF17.ThmF17
import Submission.Work.ThmF17.Closed
import Submission.Work.BSHallW.ThmF17Discharged

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF17.OddForm` — `ThmF17` with the (false at `p = 2`) Hall–Wielandt input removed

`Work.ThmF17.ThmF17` still takes `hHW : Work.ThmF.HallWielandtProp`, which audit item D2 shows is
**false at `p = 2`**.  `Work.BSHallW.thmF17'` re-runs the same §3 chain (importing
`Work.ThmF17.exp_of_chain`) with the corrected `Work.BSHallW.HallWielandtOddProp` and discharges it
with the proved `Work.BSHallW.hallWielandtOdd`.

Combining that with the App. XI reduction gives the **live form** of Théorème F — no
Hall–Wielandt hypothesis at all:

* `Work.ThmF17.thmF17_appXI_odd_of` — the three App. XI inputs in reduced form as hypotheses;
* `Work.ThmF17.thmF17_appXI_odd_closed` — those inputs *produced* (App. XI completely discharged).

`hNFp`'s shadow `NearFieldAppXIProp` is definitionally `Work.ThmF.ChV3.NearFieldAppXIProp`
(`NearFieldAppXIPropPlus.toShadow`; the bridge is `rfl`, see `AppXI/_bridge_probe.lean`); the
`AppXIProp2` / `NearFieldFieldProp` produced in `Closed.lean` are the areas' own copies, also
`rfl`-equal to `Work.ThmF17.AppXI.*`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section
open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF17

open Work.ThmF.ChV3 Work.ThmF

/-- **Théorème F, live interface**: `hFT`, `hC4`, `hTh`, `hW`, `hA`, `hHig` and the three App. XI
shadow inputs — no Hall–Wielandt hypothesis (D2 removed by `Work.BSHallW.thmF17'`). -/
theorem thmF17_appXI_odd_of (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (hTh : ThompsonFrobeniusProp) (hW : Work.ThmF.WielandtFixedPoint)
    (hA : Work.ThmF.ArithmeticNineTwoSeven) (hHig : HigmanProp)
    (hNFp : AppXI.NearFieldAppXIPropPlus) (hXI2 : AppXIProp2)
    (hNFF : NearFieldFieldProp) : ThmFProp :=
  Work.BSHallW.thmF17' hFT hC4 hTh hW hA hNFp.toShadow hXI2 hNFF hHig

/-- **Théorème F, live and App. XI-free**: no Hall–Wielandt (D2) and no App. XI input.  The
remaining hypotheses are `hFT` (Feit–Thompson), `hC4` (Ch. II §4), `hTh` (Thompson–Frobenius),
`hW` (Wielandt's fixed-point formula), `hA` (HB IX 2-7), `hHig` (Higman) and `hBrSz`
(Brauer–Suzuki, which App. XI Prop. 1 is proved from). -/
theorem thmF17_appXI_odd_closed (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (hTh : ThompsonFrobeniusProp) (hW : Work.ThmF.WielandtFixedPoint)
    (hA : Work.ThmF.ArithmeticNineTwoSeven) (hHig : HigmanProp)
    (hBrSz : BrauerSuzukiProp) : ThmFProp :=
  have hNFp : AppXI.NearFieldAppXIPropPlus :=
    Work.AppXIShadow.nearFieldAppXIPropPlus_of hFT hBrSz hC4 hTh
  have hXI2 : AppXIProp2 := Work.AppXIDickson.appXIProp2_of hNFp hFT hC4 hTh hHig
  have hNFF : NearFieldFieldProp :=
    nearFieldFieldProp_of hFT hW hTh hNFp.toShadow hXI2 hC4 hA
      (Work.AppXIField.nearFieldFieldPropNI_of hNFp)
  thmF17_appXI_odd_of hFT hC4 hTh hW hA hHig hNFp hXI2 hNFF

end Work.ThmF17

#print axioms Work.ThmF17.thmF17_appXI_odd_of
#print axioms Work.ThmF17.thmF17_appXI_odd_closed

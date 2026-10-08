import Submission.Work.ThmF17.Plumbing17
import Submission.Work.ThmF.ThmF

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF17.ThmF17` — Théorème F with `NearFieldExpProp` removed

`Work.ThmF.ThmF16` needs the App. XI input in its *complete* form
`NearFieldFullAppXIProp = NearFieldAppXIProp ∧ NearFieldExpProp`
(`ChV3/NearFieldExp.lean`).  This module delivers the same statement with only the shadow
`NearFieldAppXIProp`: the additive-group clause `NearFieldExpProp` is not an App. XI input at all,
it follows from the chain itself (`Work.ThmF17.exp_of_chain`), and the §3 assembly only ever used
it at l.160, where steps (7) and (11) are already in hand (`Work.ThmF17.chV3Prop17`).

```lean
theorem ThmF17 (hFT) (hC4) (hTh) (hW) (hHW) (hA) (hNF : NearFieldAppXIProp)
    (hXI2 : AppXIProp2) (hNFF : NearFieldFieldProp) (hHig : HigmanProp) : ThmFProp
```

`NearFieldExpProp` and `NearFieldFullAppXIProp` are no longer inputs.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF17

open Work.ThmF.ChV3 Work.ThmF

/-- **Théorème F** with the §3 chain proved and `NearFieldExpProp` no longer an input
(`ThmF16` minus `hNF.2`). -/
theorem ThmF17 (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hTh : ThompsonFrobeniusProp)
    (hW : Work.ThmF.WielandtFixedPoint) (hHW : Work.ThmF.HallWielandtProp)
    (hA : Work.ThmF.ArithmeticNineTwoSeven) (hNF : NearFieldAppXIProp)
    (hXI2 : AppXIProp2) (hNFF : NearFieldFieldProp) (hHig : HigmanProp) : ThmFProp :=
  Work.ThmF.ThmF hFT hC4 hTh hW hHW hA hNF
    (fun hFT' hC4' hTh' hW' hHW' hA' _hNF' c =>
      chV3Prop17 hFT' hC4' hTh' hW' hHW' hA' hNF hXI2 hNFF hHig c)

end Work.ThmF17

#print axioms Work.ThmF17.ThmF17

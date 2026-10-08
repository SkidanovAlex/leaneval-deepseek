import Submission.Work.ZassenhausSuzuki.Assembly
import Submission.Work.ZassenhausSuzuki.TitsAssembly
import Submission.Work.Higman.Main
import Submission.Work.Models.models

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Suzuki case with only `SuzukiTitsProp` outstanding

Area `Higman` has delivered `HigmanProp` (`Work.Higman.higmanProp`, axiom-clean, no hypotheses)
and area `Models` has delivered `ModelFactsProp` (`Work.Models.models hFT`).  Substituting both
into `zassenhausSuzuki_of_tits` shows that, beyond `FeitThompsonProp`, the **only** remaining
input of the Suzuki case of Bender–Suzuki is the Tits half `SuzukiTitsProp` (BG 5.16–5.21):

```lean
Work.ZassenhausSuzuki.zassenhausSuzuki_of_tits_only (hFT : FeitThompsonProp)
    (hT : SuzukiTitsProp) : ZassenhausSzProp
```
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- `HigmanProp` is not an extra hypothesis: it is the delivered theorem
`Work.Higman.higmanProp`. -/
theorem zassenhausSuzuki_of_tits_noHigman (hFT : FeitThompsonProp) (hMod : ModelFactsProp)
    (hT : SuzukiTitsProp) : ZassenhausSzProp :=
  zassenhausSuzuki_of_tits hFT Work.Higman.higmanProp hMod hT

/-- **The Suzuki case from `FeitThompsonProp` and the Tits half alone.** -/
theorem zassenhausSuzuki_of_tits_only (hFT : FeitThompsonProp) (hT : SuzukiTitsProp) :
    ZassenhausSzProp :=
  zassenhausSuzuki_of_tits hFT Work.Higman.higmanProp (Work.Models.models hFT) hT

/-- **The Suzuki case of Bender–Suzuki, unconditional on `FeitThompsonProp`.**  Every area
internal input is proved here: `SuzukiDataProp0` (`suzukiDataProp0_uncond`), the Tits half
(`suzukiTitsProp_live`, `TitsAssembly.lean`), the corrected `f` half (`suzukiCoordsProp`) and the
model half (`szModelDatumProp`); `HigmanProp` and `ModelFactsProp` are the delivered theorems
`Work.Higman.higmanProp` and `Work.Models.models hFT`. -/
theorem zassenhausSuzuki_final (hFT : FeitThompsonProp) : ZassenhausSzProp :=
  zassenhausSuzuki hFT Work.Higman.higmanProp (Work.Models.models hFT)
    (suzukiCoreProp_of_coords (suzukiDataProp0_uncond Work.Higman.higmanProp)
      suzukiTitsProp_live suzukiCoordsProp)
    szModelDatumProp

end Work.ZassenhausSuzuki

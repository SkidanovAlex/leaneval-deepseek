import Submission.Work.ZassenhausSuzuki.CoreV2
import Submission.Work.ZassenhausSuzuki.szA_symm_equiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `SzASymmProp` is a theorem

L5 of the lead's design note (`szA_symm_equiv`) discharges the `θ ↔ θ⁻¹` input of the
assembly, so `SuzukiCoreProp` now follows from `SuzukiDataProp0`, `SuzukiTitsProp` and
`SuzukiFProp` alone.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

theorem szASymmProp : SzASymmProp := fun m θ => szA_symm_equiv θ

/-- **The Suzuki core** from the structure half, the Tits half and the `f` half (no
`SzASymmProp` hypothesis). -/
theorem suzukiCoreProp_of_data_tits_f (hD : SuzukiDataProp0) (hT : SuzukiTitsProp)
    (hF : SuzukiFProp) : SuzukiCoreProp :=
  suzukiCoreProp_of0 szASymmProp hD hT hF

end Work.ZassenhausSuzuki

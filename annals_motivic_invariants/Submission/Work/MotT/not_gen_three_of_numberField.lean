import Submission.Work.MotT.not_gen_three_of_val
import Submission.Work.MotT.exists_val_of_numberField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Node T13 assembly: `theorem_1_2_1 (a)` on the T-route

A number field `𝕜` carries a normalized valuation `v` with `v π = vOne` (node T13,
`Work.MotT.exists_val_of_numberField`), so T10 (`Work.MotT.not_gen_three_of_val`) applies: this is
the T-route door to `theorem_1_2_1 (a)` of Lin–Shinder, an alternative to the (proved) S-route
`Work.MotR.NumberField.hasPointlessTwist_numberField`.

Nodes T7, C2, T5, T6, T9 and T13 are discharged; the only remaining input is the K-route census
`Work.MotT.LinkCertTInput` (node T8).
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- **`theorem_1_2_1 (a)` on the T-route.** -/
theorem not_gen_three_of_numberField (𝕜 : Type) [Field 𝕜] [NumberField 𝕜]
    (hlink : LinkCertTInput 𝕜) :
    ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 3 := by
  obtain ⟨v, π, hπ⟩ := exists_val_of_numberField 𝕜
  exact not_gen_three_of_val 𝕜 (by
    haveI : CharZero 𝕜 := NumberField.to_charZero
    rw [ringChar.eq_zero]
    norm_num) hlink v hπ

end

end Work.MotT

import Submission.Work.MotT.not_gen_three_of_val
import Submission.Work.MotT.exists_val_of_place

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Node T11 (`not_gen_three_of_place`): the T-route at `n = 3` for a function field with a place

A place `P : Work.FFResidual.FunctionFieldPlace 𝔽 K` of the function field `K` over the constants
`𝔽` gives a normalized valuation `v` with `v P.π = vOne` (node T11a,
`Work.MotT.exists_val_of_place`); T10 (`Work.MotT.not_gen_three_of_val`) then concludes.
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- **T11.**  The T-route conclusion for a function field with a place over its constants, in
characteristic `≠ 5`; only the K-route census `Work.MotT.LinkCertTInput` (node T8) remains as an
input. -/
theorem not_gen_three_of_place {𝔽 K : Type} [Field 𝔽] [Field K] [Algebra 𝔽 K] [Infinite K]
    (hk : ringChar K ≠ 5) (hlink : LinkCertTInput K)
    (P : Work.FFResidual.FunctionFieldPlace 𝔽 K) :
    ¬ MotivicInvariants.GenByPseudoRegularizable K 3 := by
  obtain ⟨v, hv⟩ := exists_val_of_place P
  exact not_gen_three_of_val K hk hlink v hv

end

end Work.MotT

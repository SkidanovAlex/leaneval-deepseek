import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- The explicit threshold constant `M` used in `scales_large`: `X ≥ exp M` is chosen so that
`X ^ θ ≥ 3`, `X ^ (ε ^ 2 / 2) ≥ 4`, `X ^ (ε ^ 2) ≥ 10`, `X ^ (1 - 2 * ε) ≥ 10`,
`X ^ (1 / 2 - 2 * ε) ≥ 10` and `1 ≤ Real.log X` all hold. -/
noncomputable def scalesM (θ ε : ℝ) : ℝ :=
  1 + Real.log 3 / θ + Real.log 4 / (ε ^ 2 / 2) + Real.log 10 / ε ^ 2
    + Real.log 10 / (1 - 2 * ε) + Real.log 10 / (1 / 2 - 2 * ε)

end Work.N8

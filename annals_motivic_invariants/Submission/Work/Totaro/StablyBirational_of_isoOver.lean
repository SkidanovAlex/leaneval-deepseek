import Mathlib
import Submission.Work.Totaro.Defs
import Submission.Work.K3Inputs.stablyBirat_of_isoOver
import Submission.Work.K3Inputs.StablyBiratK3

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Totaro

/-- Isomorphic varieties over `𝕜` are stably birational (`n = m = 0` in the definition of `Work.Totaro.StablyBirational`).  This is the interface fact which lets the two L-link chapters move between two models of a centre (e.g. between a centre and its base change) without re-deriving the stable birationality relation; a suitable route is `Work.K3Inputs.stablyBirat_of_isoOver` followed by `Work.K3Inputs.StablyBirat_to_stablyBirational` (which supplies the `Variety` instances of the products). -/
theorem StablyBirational_of_isoOver {𝕜 : Type} [Field 𝕜] {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y]
    (h : Work.Totaro.IsoOver 𝕜 X Y) : Work.Totaro.StablyBirational 𝕜 X Y :=
  Work.K3Inputs.StablyBirat_to_stablyBirational X Y
    (Work.K3Inputs.stablyBirat_of_isoOver 𝕜 h)

end Work.Totaro

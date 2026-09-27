import Mathlib
import Submission.Work.Mostow.ParabolicDefs
import Submission.Work.Mostow.BusemannLipschitz

/-!
# The Busemann function is `1`-Lipschitz (parabolic-fixed-point development)

The colleague's development of parabolic isometries needs the elementary fact that for every
boundary point `ξ ∈ Sph n` the Busemann function `busemann ξ = log (tpart · - ⟪·,ξ⟫)` is
`1`-Lipschitz for the hyperbolic distance.  The metric ingredient `HypIsometryProp n` is not
needed for it: the statement is pure hyperboloid algebra, and it is already available from the
barycentre chapter as `Work.Mostow.BusemannLipschitz`
(`BusemannQuad` gives the Lorentz-form quadrangle inequality `A² + B² - 2CAB ≤ 0`, and
`LogRatioArcosh` converts it into `|log A - log B| ≤ arcosh C`).  We restate it here with the
`HypIsometryProp n` hypothesis the consumer expects.
-/

namespace Work.Mostow

set_option linter.unusedVariables false in
theorem ParabolicBusemannLip (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (u v : Submission.Mostow.E n) :
    |Submission.Mostow.busemann ξ u - Submission.Mostow.busemann ξ v| ≤ Submission.Mostow.hdist u v :=
  BusemannLipschitz n ξ hξ u v

end Work.Mostow

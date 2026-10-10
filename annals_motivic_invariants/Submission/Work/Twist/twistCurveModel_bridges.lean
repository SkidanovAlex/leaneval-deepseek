import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.torsorHasPointPow_iff
import Submission.Work.Twist.torsorDivisorOfDegreePow_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The bridges of a `TwistCurveModel` hold in every presentation of the Galois group.**  A curve
model `M` of a quintic twist `D` satisfies `TwistBridges D M.C k`
(`Submission/Work/Twist/Defs.lean`) for every `k` coprime to `5`: this is the two bridge fields of
`M` transported along `torsorHasPointPow_iff` and `torsorDivisorOfDegreePow_iff`.  A caller who
only needs the descent statement, and not the curve, can therefore state it with whichever
presentation of `H¹(ℤ/5, E(L))` is convenient. -/
theorem twistCurveModel_bridges {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (M : TwistCurveModel D) {k : ℕ} (hk : k % 5 ≠ 0) :
    TwistBridges D M.C k := by
  refine ⟨?_, ?_⟩
  · exact M.hasPoint_iff.trans (torsorHasPointPow_iff D hk).symm
  · intro n
    exact (M.divisorOfDegree_iff n).trans (torsorDivisorOfDegreePow_iff D hk n).symm

end Work.Twist

import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.Assembly
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

/-- **A twist model from a curve model and the descent bridges in any presentation of the Galois
group.**  Given a `CurveModel 𝕜` (`M.C` is smooth, proper, geometrically integral of dimension
one over `𝕜`, the *geometric* half of the twist realization) and the two descent bridges written
with the generator `σ ^ k` for `k` coprime to `5`, one obtains a `TwistCurveModel` of `D`: the
scheme fields are those of `M`, and the bridge fields are the given ones transported along
`torsorHasPointPow_iff` and `torsorDivisorOfDegreePow_iff`.

This is the assembly step for the **geometric residual** `TwistRealization 𝕜`: whoever builds the
quotient `(E_L)/G` as a `CurveModel` and identifies its rational points and rational divisors with
the class of `D` in *some* presentation of `H¹(ℤ/5, E(L))` gets the full `TwistCurveModel`.  The
`k = 1` case is `twistCurveModelOf`, already proved in `Submission/Work/Twist/Assembly.lean`; the
general `k` follows from it through the two transport results
`Submission/Work/Twist/torsorHasPointPow_iff.lean` and
`Submission/Work/Twist/torsorDivisorOfDegreePow_iff.lean` (both proved). -/
theorem twistCurveModelOfPow {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (M : CurveModel 𝕜) {k : ℕ} (hk : k % 5 ≠ 0)
    (h₁ : Work.Arithmetic.HasRatPoint 𝕜 M.C ↔ QuinticTwist.TorsorHasPointPow D k)
    (h₂ : ∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 M.C n ↔
      QuinticTwist.TorsorDivisorOfDegreePow D k n) : Nonempty (TwistCurveModel D) :=
  ⟨twistCurveModelOf D M (h₁.trans (torsorHasPointPow_iff D hk))
    (fun n => (h₂ n).trans (torsorDivisorOfDegreePow_iff D hk n))⟩

end Work.Twist

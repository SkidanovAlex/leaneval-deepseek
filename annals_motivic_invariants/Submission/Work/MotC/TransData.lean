import Mathlib
import ChallengeDeps
import Submission.Work.TorsorExistence.Defs
import Submission.Work.MotC.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The translation-pullback data of the elliptic function field (audit node C2 as an interface)

This file records, as a structure, exactly the API of the pullbacks `τ_Q^*` of translations of the
elliptic function field `L(E)` that the twisted-function-field chapter (`MotC`) consumes: the group
law, the behaviour of the negation `[−1]^*`, and its compatibility with the Galois action `coeffAut`
on coefficients (`σ`).

The construction of `τ` (and the classification of the `L`-algebra automorphisms of `L(E)`) is
audit node C2, owned by the subproject `MotC2`; here it is an explicit input, so that every
statement of `MotC` that uses it can be made concrete by instantiating this structure.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotC

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- The pullback data of the elliptic function field `L(E)`: the translation pullbacks `τ_Q^*`, the
negation `[−1]^*`, and their interaction with the Galois action on coefficients. -/
structure TransData (D : Work.TorsorExistence.QuinticTwist 𝕜) where
  /-- the pullback of the translation by a point of `E(L)` -/
  τ : WeierstrassCurve.Affine.Point (baseCurve D) →
    (WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[D.ext.L]
      WeierstrassCurve.Affine.FunctionField (baseCurve D))
  /-- the pullback of `[−1]` -/
  neg : WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[D.ext.L]
    WeierstrassCurve.Affine.FunctionField (baseCurve D)
  τ_zero : τ 0 = 1
  τ_injective : Function.Injective τ
  τ_add : ∀ Q R, τ (Q + R) = (τ Q).trans (τ R)
  neg_τ : ∀ Q, (neg.trans (τ Q)).trans neg = τ (-Q)
  neg_coeff : ∀ x, neg (coeffAut D x) = coeffAut D (neg x)
  coeff_τ : ∀ (Q : WeierstrassCurve.Affine.Point (baseCurve D))
    (x : WeierstrassCurve.Affine.FunctionField (baseCurve D)),
      coeffAut D ((τ Q) x) = (τ (galPoint D Q)) (coeffAut D x)

end

end Work.MotC

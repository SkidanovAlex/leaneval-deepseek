import Mathlib
import ChallengeDeps
import Submission.Work.TorsorExistence.Defs
import Submission.Work.MotC.Coeff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The twisted function field chapter (`MotC`, audit node C1)

This is the interface of the area `Submission/Work/MotC`, whose target is the auditor's nodes
`C1` (`def twistAut`, `def twistField`, `twistField_tensor`), `C3` (`constantsOnly_all`),
`C4` (`algEquiv_ratFunc_cancel`), `C5` (`not_algEquiv_twistField`) and `C6`.

## Conventions

* `baseCurve D` (`Work.MotC.baseCurve`, in `Coeff.lean`) is the base change `E_L = E ⊗_𝕜 L` of the
  marked elliptic curve of a `QuinticTwist` datum to the cyclic quintic extension `L`.
* `Work.MotC.markPoint D` is the marked point `P ∈ E(L)` (the image of `D.P` under the base
  change `𝕜 → L`), and `Work.MotC.galPoint D` is the Galois action `σ` on the points `E(L)`.
* `Work.MotC.coeffAut D` (`Coeff.lean`) is `σ` acting on the coefficients of the function field
  `L(E) = FractionRing L[E]`.
* `Work.MotC.twistAut D τ` is the composite of the Galois action on coefficients with the pullback
  `τ` of a translation of `E(L)`:
  `twistAut D τ = (σ on coefficients) ∘ τ`.
* `Work.MotC.twistField D α` is the fixed field of a `𝕜`-algebra automorphism `α` of `L(E)`:
  the auditor's `K_P` for `α = twistAut D τ_P`.

## What is supplied and what is assumed

The pullback `τ_Q^*` of the translation by a point `Q` of `E(L)` is a `L`-algebra automorphism of
the elliptic function field `L(E)`; constructing it (and its group-law API) is node `C2`, which the
audit assigns to the separate subproject `MotC2` (its statement is phrased in terms of
`transAlgEquiv`, the very map `τ` used here).  `twistAut` therefore takes `τ` as an explicit
argument, so that everything *except* that single geometric input — in particular the descent
`twistField_sup_eq_top`/`twistField_linearDisjoint` and the fixed-field theory — is available
unconditionally.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotC

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- The marked point `P ∈ E(L)`, i.e. the image of `D.P` under the base change `𝕜 → L`. -/
noncomputable def markPoint (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    WeierstrassCurve.Affine.Point (baseCurve D) :=
  WeierstrassCurve.Affine.Point.baseChange 𝕜 D.ext.L D.P

/-- The Galois action of `σ` on the points of the base-changed curve. -/
noncomputable def galPoint (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    WeierstrassCurve.Affine.Point (baseCurve D) →+
      WeierstrassCurve.Affine.Point (baseCurve D) :=
  WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜) (F := D.ext.L) (K := D.ext.L)
    D.sigma.toAlgHom

/-- **The twisted-translation automorphism** of the auditor's node C1: the Galois action on the
coefficients of `L(E)` composed with the pullback of a translation of `E(L)`.

The intended instantiation is `τ = τ_P^*`, the pullback of the translation by the marked point `P`;
for that `τ`, the resulting `α` has order `5`, is not the identity, and restricts to `σ` on the
constants `L` (see `twistAut_algebraMap`).  In this form (`τ` an explicit `L`-algebra automorphism)
everything but the construction of `τ` is unconditional. -/
noncomputable def twistAut (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (τ : WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[D.ext.L]
      WeierstrassCurve.Affine.FunctionField (baseCurve D)) :
    WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[𝕜]
      WeierstrassCurve.Affine.FunctionField (baseCurve D) :=
  (τ.restrictScalars 𝕜).trans (coeffAut D)

/-- **The twisted function field** (audit node C1): the fixed field of the twisted-translation
automorphism.  For `α = twistAut D τ_P` this is the paper's `K_P = L(E)^{⟨σ ⊗ τ_P^*⟩}`, the
function field of the quintic twist of `E` by the marked point. -/
noncomputable def twistField (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (α : WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[𝕜]
      WeierstrassCurve.Affine.FunctionField (baseCurve D)) :
    IntermediateField 𝕜 (WeierstrassCurve.Affine.FunctionField (baseCurve D)) :=
  IntermediateField.fixedField (Subgroup.zpowers α)

end

end Work.MotC

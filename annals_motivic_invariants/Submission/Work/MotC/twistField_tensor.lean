import Mathlib
import ChallengeDeps
import Submission.Work.TorsorExistence.Defs
import Submission.Work.MotC.Defs
import Submission.Work.MotC.twistAut_algebraMap
import Submission.Work.MotC.fixedField_descent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The descent of the twisted function field (audit node C1, `twistField_tensor`)

For a twisted-translation automorphism `α = twistAut D τ = (σ on coefficients) ∘ τ` of `L(E)` of
order `5`, the twisted function field `K_P = twistField D α` — the fixed field of `α` — satisfies
the Galois descent

* `K_P` and `L` are linearly disjoint over `𝕜`,
* `K_P · L = L(E)` (their compositum is everything),
* `[L(E) : K_P] = 5`,

the three statements together being equivalent to the auditor's
`twistField D Q ⊗[𝕜] L ≃ₐ[L] (E_L).FunctionField` (the multiplication map
`K_P ⊗[𝕜] L → L(E)` is injective by linear disjointness, and surjective because its image is the
compositum `K_P ⊔ L = ⊤`).  The literal tensor-product form `A ⊗[𝕜] L ≃ₐ[𝕜] K` (a `𝕜`-algebra
isomorphism, together with its two `tmul` equations) is
`Work.MotC.C6.exists_tensorAlgEquiv`, in `Submission/Work/MotC/C6/exists_tensorAlgEquiv.lean`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotC

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- **Audit node C1, the descent.**  An order-five twisted-translation automorphism `α` of `L(E)`
which restricts to the Galois generator `σ` on the constants `L` has fixed field `K_P = twistField D
α` with `K_P ⊗[𝕜] L ≅ L(E)`; stated here as the three equivalent pieces (linear disjointness, the
compositum, and the degree). -/
theorem twistField_tensor (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (τ : WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[D.ext.L]
      WeierstrassCurve.Affine.FunctionField (baseCurve D))
    (h5 : (twistAut D τ) ^ 5 = 1) (hne : twistAut D τ ≠ 1) :
    (twistField D (twistAut D τ)).LinearDisjoint D.ext.L ∧
      twistField D (twistAut D τ) ⊔
          (IsScalarTower.toAlgHom 𝕜 D.ext.L
            (WeierstrassCurve.Affine.FunctionField (baseCurve D))).fieldRange = ⊤ ∧
        Module.finrank ↥(twistField D (twistAut D τ))
          (WeierstrassCurve.Affine.FunctionField (baseCurve D)) = 5 :=
  fixedField_descent D.ext _ (twistAut D τ) h5 hne (fun l => twistAut_algebraMap D τ l)

end

end Work.MotC

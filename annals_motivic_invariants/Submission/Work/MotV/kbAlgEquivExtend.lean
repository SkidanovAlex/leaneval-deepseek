import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- Every `𝕜`-algebra automorphism `α` of `RatFunc 𝕜` extends to a `𝕜`-algebra automorphism `σ` of
`Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)`.  `IsAlgClosure.equivOfEquiv` gives a ring equivalence of the
algebraic closures intertwining the `algebraMap`s; `AlgEquiv.ofRingEquiv` upgrades it, 𝕜-linearity
being `α.commutes`. -/
theorem kbAlgEquivExtend {𝕜 : Type} [Field 𝕜] (α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) :
    ∃ σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜,
      ∀ c : RatFunc 𝕜,
        σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
          = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (α c) := by
  -- `IsAlgClosure.equivOfEquiv` produces the ring equivalence of the two algebraic closures
  -- (here the same one, `Kb 𝕜`) intertwining the `algebraMap`s along `α`.
  let e : Work.MotV.Kb 𝕜 ≃+* Work.MotV.Kb 𝕜 :=
    IsAlgClosure.equivOfEquiv (Work.MotV.Kb 𝕜) (Work.MotV.Kb 𝕜) α.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := e) ?_, ?_⟩
  · -- 𝕜-linearity: `e` fixes the image of `𝕜`, because `α` does.
    intro x
    rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜)]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    exact congrArg (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) (α.commutes x)
  · -- the intertwining property, transported through `AlgEquiv.ofRingEquiv`
    intro c
    exact IsAlgClosure.equivOfEquiv_algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Kb 𝕜)
      α.toRingEquiv c

end Work.MotV

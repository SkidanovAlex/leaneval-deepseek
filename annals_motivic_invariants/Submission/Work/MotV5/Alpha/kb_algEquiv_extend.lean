import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Alpha

/-- **Extension of a `𝕜`-automorphism of `RatFunc 𝕜` to its algebraic closure.**  For every
`α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜` there is a `𝕜`-algebra automorphism `σ` of
`Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)` acting on the constants by `α`. -/
theorem kb_algEquiv_extend (𝕜 : Type) [Field 𝕜] (α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) :
    ∃ σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜,
      ∀ c : RatFunc 𝕜,
        σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
          = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (α c) := by
  -- `IsAlgClosure.equivOfEquiv` lifts the ring equivalence `α` of the base fields to a ring
  -- equivalence of the algebraic closures, intertwining the two `algebraMap`s.
  let e : Work.MotV.Kb 𝕜 ≃+* Work.MotV.Kb 𝕜 :=
    IsAlgClosure.equivOfEquiv (Work.MotV.Kb 𝕜) (Work.MotV.Kb 𝕜) α.toRingEquiv
  have he : ∀ c : RatFunc 𝕜,
      e (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
        = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (α c) :=
    fun c => IsAlgClosure.equivOfEquiv_algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Kb 𝕜)
      α.toRingEquiv c
  refine ⟨AlgEquiv.ofRingEquiv (R := 𝕜) (f := e) ?_, he⟩
  -- `𝕜`-linearity: `e` fixes the image of `𝕜`, because `α` does.
  intro x
  rw [show algebraMap 𝕜 (Work.MotV.Kb 𝕜) x
        = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (algebraMap 𝕜 (RatFunc 𝕜) x) from rfl,
    he, AlgEquiv.commutes]

end Work.MotV5.Alpha

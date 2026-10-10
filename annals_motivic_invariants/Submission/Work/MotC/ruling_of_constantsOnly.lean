import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotC.not_algEquiv_ratFunc_twistField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Constants-only implies the ruling hypothesis (node CR6)

`Work.MotC.RulingStable 𝕜 A B` (the residual of node C6 (iii)) asks that every `𝕜`-isomorphism
`RatFunc A ≃ₐ[𝕜] RatFunc B` carry the constants `A` into the constants `B`.  If `A` is
constants-only over `𝕜` (`Work.MotV.ConstantsOnly 𝕜 A`) then this holds: composing the isomorphism
with the inclusion `A ↪ RatFunc A` gives a `𝕜`-embedding of `A` into `RatFunc B`, whose image is a
constant by constants-only.
-/

set_option autoImplicit false

namespace Work.MotC

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

-- `Work.MotV.ConstantsOnly` quantifies over `M : Type`, so the fields below live in `Type`.

/-- **Audit node CR6.**  Constants-only gives the ruling hypothesis of
`Work.MotC.algEquiv_ratFunc_cancel`. -/
theorem ruling_of_constantsOnly {A B : Type} [Field A] [Field B] [Algebra 𝕜 A] [Algebra 𝕜 B]
    (hCO : Work.MotV.ConstantsOnly 𝕜 A) (θ : RatFunc A ≃ₐ[𝕜] RatFunc B) (a : A) :
    ∃ b : B, θ (algebraMap A (RatFunc A) a) = algebraMap B (RatFunc B) b := by
  obtain ⟨c, hc⟩ := hCO B (θ.toAlgHom.comp (IsScalarTower.toAlgHom 𝕜 A (RatFunc A))) a
  exact ⟨c, hc.symm⟩

/-- `RulingStable` follows from constants-only. -/
theorem rulingStable_of_constantsOnly {A B : Type} [Field A] [Field B] [Algebra 𝕜 A]
    [Algebra 𝕜 B] (hCO : Work.MotV.ConstantsOnly 𝕜 A) : RulingStable 𝕜 A B :=
  fun θ a => ruling_of_constantsOnly hCO θ a

end

end Work.MotC

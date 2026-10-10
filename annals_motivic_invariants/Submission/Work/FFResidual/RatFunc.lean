/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Main
import Submission.Work.FFResidual.hasFunctionFieldPlace_ratFunc

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The residual at the rational function field, by the place route

The place of `𝔽(t)` at `t = 0` (`hasFunctionFieldPlace_ratFunc`) feeds the local theory of this
area: the residual `Work.ClassBCD.FunctionFieldResidual 𝔽 (RatFunc 𝔽)` and the arithmetic half
`Work.PointlessTwist.HasPointlessTwist (RatFunc 𝔽)` follow from the Kummer/Artin–Schreier local
analysis at that place — an independent proof of the case which `Work.ClassBCD.RatFunc` closes
through the classical `E(𝔽(t)) = E(𝔽)` (`ConstantsOnly`).  (In characteristic `5`, the Artin–Schreier
route `nonempty_functionFieldResidual_ratFunc_charP` applies to the same place.)
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.FFResidual

noncomputable section

/-- **The residual at `𝕜 = 𝔽(t)`, by the place route** (characteristic `≠ 5`, `ζ₅ ∈ 𝔽`). -/
theorem nonempty_functionFieldResidual_ratFunc (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 (RatFunc 𝔽)) :=
  (hasFunctionFieldPlace_ratFunc 𝔽).some.nonempty_functionFieldResidual ζ hζ c hΔ hj

/-- **The arithmetic half at `𝕜 = 𝔽(t)`**, by the place route. -/
theorem nonempty_hasPointlessTwist_ratFunc (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq (RatFunc 𝔽), @Work.PointlessTwist.HasPointlessTwist (RatFunc 𝔽) _ dec :=
  (hasFunctionFieldPlace_ratFunc 𝔽).some.nonempty_hasPointlessTwist_of_place ζ hζ c hΔ hj

/-- **The residual at `𝕜 = 𝔽(t)` in characteristic five**, by the Artin–Schreier place route. -/
theorem nonempty_functionFieldResidual_ratFunc_charP (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽]
    [CharP 𝔽 5] (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 (RatFunc 𝔽)) := by
  haveI : CharP (RatFunc 𝔽) 5 :=
    charP_of_injective_algebraMap (algebraMap 𝔽 (RatFunc 𝔽)).injective 5
  exact (hasFunctionFieldPlace_ratFunc 𝔽).some.nonempty_functionFieldResidual_charP c hΔ hj

end

end Work.FFResidual

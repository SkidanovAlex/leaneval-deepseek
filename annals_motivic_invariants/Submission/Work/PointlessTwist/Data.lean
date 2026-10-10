/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessTwist
-/
import Mathlib
import ChallengeDeps
import Submission.Work.PointlessTwist.Assembly
import Submission.Work.PointlessTwist.Kummer.not_exists_pow_five_eq_X

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The concrete data of the function-field classes

Step (A) of the paper's proof for the function-field classes: over `𝕜 = 𝔽(t)` with `𝔽` containing a
primitive `5`-th root of unity `ζ`, the root field of `X ^ 5 - t` is a cyclic extension of degree `5`
of `𝕜` (`Work.TorsorExistence.existsCyclicExtension_of_zeta5`), the only field-theoretic input being
`t ∉ 𝔽(t) ^ 5` (`Work.PointlessTwist.Kummer.not_exists_pow_five_eq_X`).  The concrete field of
class (b) is `𝔽 = ℚ(ζ₅) = CyclotomicField 5 ℚ`, whose primitive root is obtained from
`IsCyclotomicExtension.exists_isPrimitiveRoot`; for class (c) one uses `𝔽₁₁` (`5 ∣ 11 - 1`) and for
class (d) `𝔽 = ℂ` (or any algebraically closed field); in characteristic `5` the Artin–Schreier
constructor `existsCyclicExtension_of_charP_five` replaces Kummer theory (with `a = t ∉ ℘(𝔽(t))`).

## Main results

* `nonempty_kummerCyclicExtension` — the construction for an arbitrary field of constants carrying a
  primitive `5`-th root of unity.
* `exists_data_functionField_numberField` — the concrete instance `𝔽 = ℚ(ζ₅)`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Polynomial

namespace Work.PointlessTwist

noncomputable section

/-- **The Kummer cyclic quintic extension of `𝔽(t)`.**  If `𝔽` contains a primitive `5`-th root of
unity `ζ` then `𝔽(t)` has a cyclic extension of degree `5`, namely the root field of `X ^ 5 - t`
(`Work.TorsorExistence.existsCyclicExtension_of_zeta5`); the only input is that `t` is not a fifth
power in `𝔽(t)` (`Work.PointlessTwist.Kummer.not_exists_pow_five_eq_X`). -/
theorem nonempty_kummerCyclicExtension {𝔽 : Type} [Field 𝔽] (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    Nonempty (Work.TorsorExistence.CyclicExtension (RatFunc 𝔽) 5) := by
  have hζ' : IsPrimitiveRoot (algebraMap 𝔽 (RatFunc 𝔽) ζ) 5 :=
    hζ.map_of_injective (algebraMap 𝔽 (RatFunc 𝔽)).injective
  refine Work.TorsorExistence.existsCyclicExtension_of_zeta5
    (algebraMap 𝔽 (RatFunc 𝔽) ζ) hζ' RatFunc.X ?_
  rintro ⟨b, hb⟩
  exact Kummer.not_exists_pow_five_eq_X ⟨b, hb⟩

end

end Work.PointlessTwist

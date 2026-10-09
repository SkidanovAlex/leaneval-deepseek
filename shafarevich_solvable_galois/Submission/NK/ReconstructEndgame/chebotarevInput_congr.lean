import Mathlib
import Submission.NK.ReconstructEndgame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `ℚ`-algebra form of Čebotarev's input agrees with the plain form

`NK.ReconstructEndgame.ChebotarevInputDerived K K'` (see `Basic.lean`) is
`NK.Reconstruct.ChebotarevInput ℚ K'` stated with the `ℚ`-algebra structure on `K'` replaced by
the canonical one `NK.ReconstructEndgame.ratAlgebra K K'` derived from the number field `K`.

The two forms are logically equivalent: there is at most one `ℚ`-algebra structure on a commutative
ring (`Subsingleton (Algebra ℚ K')`, since a ring homomorphism out of the prime field `ℚ` is unique
and the scalar action is determined by it), so the instance appearing in `ChebotarevInput` may be
replaced by the ambient `inferInstance`; the remaining parameter of `ChebotarevInput` (the
`NumberField ℚ` instance) is the same on both sides.

This lemma lets a caller state Čebotarev's input in the plain `NK.Reconstruct` vocabulary (with an
ambient `Algebra ℚ K'`) and use it where `ChebotarevInputDerived` is expected, and conversely — in
particular it is the bridge that turns the `ℚ`-algebra form of the Čebotarev hypothesis used in the
assembly chapter `Submission/Work/ReconstructEndgame/Main.lean` into the plain form consumed by
`NK.Reconstruct.exists_sigma_of_localCorrespondence`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NK.ReconstructEndgame

theorem chebotarevInput_congr (K K' : Type*) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Algebra ℚ K'] :
    NK.Reconstruct.ChebotarevInput ℚ K' ↔ ChebotarevInputDerived K K' := by
  unfold ChebotarevInputDerived
  constructor <;> intro h <;> convert h using 2 <;> exact Subsingleton.elim _ _

end NK.ReconstructEndgame

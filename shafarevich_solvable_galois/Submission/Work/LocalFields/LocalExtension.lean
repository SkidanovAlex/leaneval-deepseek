/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `K_v ⊆ L_w` as an extension of local fields

With the canonical algebra structure on `L_w` over `K_v`
(`Work.LocalFields.CompletionHom.completionAlgebra`) we obtain, from
`Work.LocalFields.hasExtension_completion`, that the `w`-adic valuation of `L_w` extends the
`v`-adic valuation of `K_v` and hence that `L_w/K_v` is an extension of local fields in the sense
of `Work.LocalFields.IsLocalFieldExtension`.  This makes the local notion of unramified,
`Work.LocalFields.IsUnramifiedLocalExtension`, available for the completions.

## Main definitions

* `Work.LocalFields.instHasExtensionCompletion`
* `Work.LocalFields.instIsLocalFieldExtensionCompletion`

## Main results

* `Work.LocalFields.isUnramifiedAt_iff_isUnramifiedLocalExtension` (sibling file).
-/
import Submission.Work.LocalFields.Inputs
import Submission.Work.LocalFields.CompletionExtension
import Submission.Work.LocalFields.hasExtension_completion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The `v`-adic valuation on `K_v` extends the `w`-adic valuation on `L_w`. -/
noncomputable instance instHasExtensionCompletion (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Valuation.HasExtension (Valued.v (R := Completion K v)) (Valued.v (R := Completion L w)) :=
  hasExtension_completion v w

/-- `L_w` is a valued extension of `K_v`. -/
instance instIsLocalFieldExtensionCompletion (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    IsLocalFieldExtension (Completion K v) (Completion L w) where
  hasExtension := instHasExtensionCompletion v w

end Work.LocalFields

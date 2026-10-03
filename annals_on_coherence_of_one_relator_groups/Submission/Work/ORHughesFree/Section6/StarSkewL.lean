/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `∗`-ring structure on the skew Laurent polynomial ring `U[t^{±1};τ]`

Mathlib has no `StarRing` instance on `SkewMonoidAlgebra U (Multiplicative ℤ)`.  For the twist
`τ` of [JZLA20] the correct involution is `starSkewL` (`t^* = t^{-1}`, coefficients twisted by the
`ℤ`-action), which is a `∗`-ring structure as soon as the action commutes with `star`
(`NaturalExtension.StarAction`).  We install it as an instance so that the uniqueness theorem for
epic `∗`-regular envelopes (`EpicEnvelopeUnique`) can be applied to the ring
`U[t^{±1};τ]`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.starSkewLaurent

set_option autoImplicit false

namespace Work.ORHughesFree

/-- The involution `starSkewL` of the skew Laurent polynomial ring, as a `StarRing` instance. -/
@[reducible] noncomputable instance instStarRingSkewMonoidAlgebra {U : Type} [Ring U] [StarRing U]
    [MulSemiringAction (Multiplicative ℤ) U] [NaturalExtension.StarAction U] :
    StarRing (SkewMonoidAlgebra U (Multiplicative ℤ)) where
  star := NaturalExtension.starSkewL
  star_involutive := NaturalExtension.starSkewL_involutive
  star_mul := NaturalExtension.starSkewL_mul
  star_add := NaturalExtension.starSkewL_add

end Work.ORHughesFree

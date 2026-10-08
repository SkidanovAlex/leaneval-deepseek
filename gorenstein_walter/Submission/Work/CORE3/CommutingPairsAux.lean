import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE2A.Basic

/-!
# Auxiliary vocabulary for `Work.CORE3.CommutingPairsEqCosetSum`

Bender 1981 §3 (8) counts the pairs `(z, s)` of commuting involutions with `z ∉ Ĥ` and
`s ∈ Ĥ`.  Equivalently, such a pair is the same thing as a pair of *distinct commuting
involutions both outside* `Ĥ` lying in a common coset of `Ĥ`: the bijection is

  `(z, s) ↦ (z, z * s)`      (the "shear" `pairShear`),

with inverse `(z, z') ↦ (z, z⁻¹ * z')`.

This module fixes that vocabulary, so that the two halves of the identity

  `(commutingPairsOutsideHat B).ncard = Σ_{c ≠ 1} cosetPairCount B.Hhat (Quotient.out c)`

can be stated and proved separately:

* `pairShear` — the shear `(z, s) ↦ (z, z * s)` on `G × G`;
* `commutingPairsSameCoset B` — pairs of distinct commuting involutions outside `B.Hhat`
  lying in a common coset of `B.Hhat`.
-/

namespace Work.CORE3

open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-- The shear `(z, s) ↦ (z, z * s)` on `G × G`.  It is a bijection (with inverse
`(z, z') ↦ (z, z⁻¹ * z')`) and carries `Work.CORE3.commutingPairsOutsideHat B` onto
`Work.CORE3.commutingPairsSameCoset B`. -/
def pairShear (p : G × G) : G × G := (p.1, p.1 * p.2)

/-- The set of pairs `(z, z')` of *distinct commuting involutions outside* `B.Hhat` which lie
in a common coset of `B.Hhat`.  This is the image of `Work.CORE3.commutingPairsOutsideHat B`
under the shear `Work.CORE3.pairShear`. -/
def commutingPairsSameCoset (B : BenderSetup G) : Set (G × G) :=
  {p : G × G | (QuotientGroup.mk p.1 : G ⧸ B.Hhat) = QuotientGroup.mk p.2 ∧
    p.1 ≠ p.2 ∧ p.1 * p.2 = p.2 * p.1 ∧ p.1 ∈ involsOutsideHat B ∧ p.2 ∈ involsOutsideHat B}

end Work.CORE3

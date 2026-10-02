import Mathlib
import Submission.Work.Gen.Basic
import Submission.Work.Thom.chernClass
import Submission.Work.Gen.tautDual_euler_neg

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The first Chern class of the tautological line bundle and of its dual

`Work.Thom.chernClass 1 1 Z` of a rank-one complex bundle `Z` is the top Chern class, i.e. the
Euler class of the canonical Thom class of the realification
(`Work.Thom.chernClass_one_top`).  For the tautological line bundle `O(-1) = Work.Gen.tautLine n`
and its dual `O(1) = Work.Gen.tautDual n` over `ℂPⁿ`, the complex conjugation of the fibre is an
orientation reversing real isomorphism, so the two Euler classes differ by a sign
(`Work.Gen.tautDual_euler_neg`, the sign lemma of this area).  Hence

  `c₁(O(-1)) = −c₁(O(1))`,

which is the normalisation that the Euler-sequence computation of the Chern classes of `TℂPⁿ`
uses.
-/

namespace Work.Gen

theorem chernClass_tautLine (n : ℕ) :
    Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)
      = - Work.Thom.chernClass 1 1 (Work.Gen.tautDual n) := by
  rw [Work.Thom.chernClass_one_top (tautLine n), Work.Thom.chernClass_one_top (tautDual n)]
  rw [tautDual_euler_neg n]
  abel

end Work.Gen

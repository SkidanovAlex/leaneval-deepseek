import Mathlib
import Submission.Work.Gen.Basic
import Submission.Work.Gen.ConjLine
import Submission.Work.Gen.tautDual_iso_conjLine
import Submission.Work.Gen.conjLine_euler_neg
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.thomClassRank_eulerClass_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

namespace Work.Gen

/-- **`c₁(O(1)) = −c₁(O(-1))` on `ℂPⁿ`**, in the form of the Euler classes of the rank-one
canonical Thom classes: the dual tautological line bundle `O(1) = Work.Gen.tautDual n` and the
tautological line bundle `O(-1) = Work.Gen.tautLine n` differ by the sign of the complex
orientation.

`O(1)` is the complex conjugate of `O(-1)` (`Work.Gen.tautDual_iso_conjLine`), and the conjugate of
a complex line bundle has the negative first Chern class (the fibrewise complex conjugation is an
orientation reversing real isomorphism, `Work.Gen.conjLine_euler_neg`); this is the sign lemma that
fixes the normalisation of the hyperplane class `u = c₁(O(1))` in the Euler-sequence computations
of this area. -/
theorem tautDual_euler_neg (n : ℕ) :
    (Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0)) (tautDual n)).eulerClass
      = - (Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0)) (tautLine n)).eulerClass := by
  obtain ⟨e⟩ := tautDual_iso_conjLine n
  rw [Work.Thom.thomClassRank_eulerClass_iso (tautDual n) (conjLine n) e (le_refl 1)]
  exact conjLine_euler_neg n

end Work.Gen

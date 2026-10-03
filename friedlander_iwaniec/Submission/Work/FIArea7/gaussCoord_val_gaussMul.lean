import Mathlib
import Submission.Work.FIArea7.GaussUnits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- Coordinate-wise, the Gaussian product of `p q` has coordinates congruent mod `n`
to the complex product of the representatives `p.1.val + i p.2.val`,
`q.1.val + i q.2.val`. -/
theorem gaussCoord_val_gaussMul (n : ℕ) (hn : 0 < n) (p q : ZMod n × ZMod n) :
    ((Work.FIArea7.gaussMul p q).1.val : ℤ) ≡ (p.1.val : ℤ) * (q.1.val : ℤ) - (p.2.val : ℤ) * (q.2.val : ℤ) [ZMOD (n : ℤ)] ∧
    ((Work.FIArea7.gaussMul p q).2.val : ℤ) ≡ (p.1.val : ℤ) * (q.2.val : ℤ) + (p.2.val : ℤ) * (q.1.val : ℤ) [ZMOD (n : ℤ)] := by
  have hnz : NeZero n := ⟨hn.ne'⟩
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp only [gaussMul, ZMod.natCast_zmod_val]
  · rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp only [gaussMul, ZMod.natCast_zmod_val]

end Work.FIArea7

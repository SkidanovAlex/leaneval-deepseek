import Mathlib
import Submission.Work.CNum.Fx

/-!
# `Work.CNum.SmallBox` — the "small box" predicate for the CNum chord data

`absMax I = max |I.lo| |I.hi|` (in mantissas).  A box (`Cpx`) is `Small` when both of its
coordinate mantissas are bounded by `2^32`: the side condition under which the mantissa-level
square root `sqUp` used by `distUp` stays inside its `70`-step binary-search range.
-/

namespace Work.CNum

open Work.ANum

/-- A box whose coordinate mantissas are bounded by `2^32`. -/
def Small (p : Cpx) : Prop := absMax p.re ≤ 2 ^ 32 ∧ absMax p.im ≤ 2 ^ 32

lemma absMax_nonneg (I : Iv) : 0 ≤ absMax I := by
  rw [absMax]
  exact le_trans (Int.natCast_nonneg _) (le_max_left _ _)

end Work.CNum

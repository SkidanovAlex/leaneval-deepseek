import Mathlib
import Submission.Work.IntLib.intDivAPI

/-!
# Floor division by a power of two

`Int.fdiv` rounds towards `-∞`.  Since `2 ^ k` is a strictly positive divisor, the floor
quotient of `a` is computed from the natural division of `|a|` by `2 ^ k`, rounding *up* when
`a < 0` and `|a|` is not divisible by `2 ^ k` (the ceiling `⌈|a| / 2 ^ k⌉` appears with a sign).

This is the arithmetic fact underlying the `shrF` shift word of `Work.IntLib`.
-/

namespace Work.IntLib.Shift

/-- Floor division by `2 ^ k`, in terms of the natural division and remainder of `natAbs a`. -/
theorem fdivPow2 (a : ℤ) (k : ℕ) :
    a.fdiv ((2 : ℤ) ^ k) =
      (if a < 0 then -(((a.natAbs / 2 ^ k) + (if a.natAbs % 2 ^ k = 0 then 0 else 1) : ℕ) : ℤ)
        else ((a.natAbs / 2 ^ k : ℕ) : ℤ)) := by
  have hb : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
  have hna : ((2 : ℤ) ^ k).natAbs = 2 ^ k := by simp [Int.natAbs_pow]
  -- `Work.IntLib.intDivAPI` gives the floor quotient of an arbitrary positive divisor.
  have h := Work.IntLib.intDivAPI.2.2.1 a ((2 : ℤ) ^ k) hb
  rw [h, hna]
  rcases lt_or_ge a 0 with ha | ha
  · -- `a < 0`: the floor quotient is the negative of the ceiling `⌈|a| / 2 ^ k⌉`.
    rw [ite_eq_right (not_le.mpr ha), ite_eq_left ha]
    by_cases hc : a.natAbs % 2 ^ k = 0 <;> simp [hc, Nat.cast_add]
  · -- `a ≥ 0`: floor quotient and natural quotient agree.
    rw [ite_eq_left ha, ite_eq_right (not_lt.mpr ha)]

end Work.IntLib.Shift

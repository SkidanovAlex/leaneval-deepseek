import Mathlib

namespace Work.IntLib.Shift

/-- Truncated division of a natural, coerced to `ℤ`, by a power of two. -/
lemma tdiv_pow2_natCast (n k : ℕ) :
    ((n : ℤ)).tdiv ((2 : ℤ) ^ k) = ((n / 2 ^ k : ℕ) : ℤ) := by
  rw [Int.natCast_tdiv_eq_ediv]
  exact (Int.natCast_ediv n (2 ^ k)).symm

/-- Truncated division by `2 ^ k`: since `2 ^ k > 0`, the quotient has the sign of `a`
and is `±(a.natAbs / 2 ^ k)`. -/
theorem tdivPow2 (a : ℤ) (k : ℕ) :
    a.tdiv ((2 : ℤ) ^ k) = (if a < 0 then -1 else 1) * ((a.natAbs / 2 ^ k : ℕ) : ℤ) := by
  rcases lt_or_ge a 0 with ha | ha
  · have hb : (if a < 0 then (-1 : ℤ) else 1) = -1 := by simp [ha]
    rw [hb]
    have hneg : a = -((a.natAbs : ℕ) : ℤ) := by
      rcases Int.natAbs_eq a with h | h
      · rw [h] at ha
        exact absurd ha (not_lt.mpr (Int.natCast_nonneg a.natAbs))
      · exact h
    conv_lhs => rw [hneg]
    rw [Int.neg_tdiv, tdiv_pow2_natCast, neg_one_mul]
  · have hb : (if a < 0 then (-1 : ℤ) else 1) = 1 := by simp [ha]
    rw [hb, one_mul]
    have hpos : a = ((a.natAbs : ℕ) : ℤ) := (Int.natAbs_of_nonneg ha).symm
    conv_lhs => rw [hpos]
    rw [tdiv_pow2_natCast]

end Work.IntLib.Shift

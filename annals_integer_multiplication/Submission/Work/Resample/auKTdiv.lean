import Mathlib
import Submission.Work.Resample.auPrepDefs

/-!
# `auK` as a truncated quotient

`auK s t k = (2*k*s + t) / (2*t)` (the window centre of the resampling table, paper §4) is the
result of the integer truncated division performed by the record word: the value it computes with
`tdiv` is exactly `auK s t k`, and the same holds for the *next* centre `auK s t (k+1)`, whose
numerator is `2*k*s + t + 2*s`.

Both facts reduce to the elementary identity `Int.tdiv (m:ℤ) (n:ℤ) = (m/n : ℕ)` for nonnegative
`m`, `n`, which is `Int.tdiv_eq_ediv` together with `Int.natCast_div`.
-/

namespace Work.Resample

/-- `Int.tdiv` of two natural casts is the natural division, cast back. -/
theorem int_tdiv_natCast (m n : ℕ) :
    Int.tdiv (m : ℤ) (n : ℤ) = ((m / n : ℕ) : ℤ) := by
  rw [Int.tdiv_eq_ediv, ite_eq_left (Or.inl (Int.natCast_nonneg m)), add_zero]
  exact (Int.natCast_div m n).symm

theorem auKTdiv (s t k : ℕ) (ht : 0 < t) :
    Int.tdiv ((2 : ℤ) * (k : ℤ) * (s : ℤ) + (t : ℤ)) ((2 : ℤ) * (t : ℤ))
        = ((Work.Resample.auK s t k : ℕ) : ℤ) ∧
    Int.tdiv (((2 : ℤ) * (k : ℤ) * (s : ℤ) + (t : ℤ)) + 2 * (s : ℤ)) ((2 : ℤ) * (t : ℤ))
        = ((Work.Resample.auK s t (k + 1) : ℕ) : ℤ) := by
  have hden : ((2 * t : ℕ) : ℤ) = (2 : ℤ) * (t : ℤ) := by push_cast; ring
  have hnum1 : ((2 * k * s + t : ℕ) : ℤ) = (2 : ℤ) * (k : ℤ) * (s : ℤ) + (t : ℤ) := by
    push_cast; ring
  have hnum2 : ((2 * (k + 1) * s + t : ℕ) : ℤ)
      = ((2 : ℤ) * (k : ℤ) * (s : ℤ) + (t : ℤ)) + 2 * (s : ℤ) := by
    push_cast; ring
  constructor
  · rw [← hnum1, ← hden, int_tdiv_natCast]
    rfl
  · rw [← hnum2, ← hden, int_tdiv_natCast]
    rfl

end Work.Resample

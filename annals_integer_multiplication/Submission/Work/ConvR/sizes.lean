import Mathlib
import Submission.Work.ConvR.basic

/-!
# Sizes of encoded values on stack 0 (ConvR support)

Small size facts used by `Submission/Work/ConvR/listProd.lean` (the list-product word):

* `Nat.size` is subadditive under multiplication;
* `isz` of a product of naturals is at most the sum of the `isz`'s;
* the encoding size of a list of naturals is the sum of the `isz`'s plus the length plus one;
* every `isz` is at least `2` and every `vsz` is at least `1`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

theorem nat_size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem isz_mul_nat_le (a b : ℕ) : isz ((a * b : ℕ) : ℤ) ≤ isz (a : ℤ) + isz (b : ℤ) := by
  have h := nat_size_mul_le a b
  simp only [isz, Int.natAbs_natCast]
  omega

/-- The `map` of `isz` over a cons, in the syntactic form produced by
`ts.map fun t => isz (t : ℤ)` (an ascription inside an unannotated `fun` elaborates through
`List.bind`/`List.flatMap`, so `List.map_cons` does not fire on it). -/
theorem map_isz_cons (t : ℕ) (ts : List ℕ) :
    ((t :: ts).map fun t => isz (t : ℤ)) = isz (t : ℤ) :: (ts.map fun t => isz (t : ℤ)) := by
  simp only [List.map_eq_flatMap, List.bind_eq_flatMap, List.flatMap_cons]
  rfl

theorem sum_map_isz_cons (t : ℕ) (ts : List ℕ) :
    ((t :: ts).map fun t => isz (t : ℤ)).sum =
      isz (t : ℤ) + (ts.map fun t => isz (t : ℤ)).sum := by
  rw [map_isz_cons]; simp

theorem vsz_intList_cons (t : ℕ) (ts : List ℕ) :
    vsz (intList (t :: ts)) = isz (t : ℤ) + vsz (intList ts) + 1 := by
  rw [show intList (t :: ts) = Val.cons (Val.int (t : ℤ)) (intList ts) from rfl, vsz_cons, vsz_int]

theorem vsz_intList (ts : List ℕ) :
    vsz (intList ts) = (ts.map fun t => isz (t : ℤ)).sum + ts.length + 1 := by
  induction ts with
  | nil => simp [intList, ofList, vsz, Val.enc]
  | cons t ts ih =>
    rw [vsz_intList_cons, ih, sum_map_isz_cons]
    simp only [List.length_cons]
    ring

theorem vsz_one_le (v : Val) : 1 ≤ vsz v := by
  cases v with
  | int z => simp only [vsz, Val.enc, List.length_cons]; omega
  | nil => simp [vsz, Val.enc]
  | cons a b => simp only [vsz, Val.enc, List.length_cons]; omega

theorem two_le_isz (z : ℤ) : 2 ≤ isz z := by simp [isz]

end Work.ConvR

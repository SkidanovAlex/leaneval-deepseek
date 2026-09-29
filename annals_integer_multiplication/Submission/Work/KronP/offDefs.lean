import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.KronP.math

/-!
# KronP: the `ℕ`-valued shadow of the digit offset

`digitOffset p N = Σ_{m<N} T·B^m` with `T = 2^{3p-1}` and `B = 2^{3p}` is an integer sum of
nonnegative terms.  `offNat p N` is the same sum computed in `ℕ`; it is the convenient object for
the arithmetic bounds needed by `Work.KronP.prodOffset`.
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-- `Σ_{m<N} 2^{3p-1}·(2^{3p})^m`, computed in `ℕ`. -/
def offNat (p N : ℕ) : ℕ :=
  ((List.range N).map fun m => 2 ^ (3 * p - 1) * (2 ^ (3 * p)) ^ m).sum

@[simp] theorem offNat_zero (p : ℕ) : offNat p 0 = 0 := rfl

/-- The recursion step of `offNat`. -/
theorem offNat_succ (p N : ℕ) :
    offNat p (N + 1) = offNat p N + 2 ^ (3 * p - 1) * (2 ^ (3 * p)) ^ N := by
  unfold offNat
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- The recursion step of `digitOffset`. -/
theorem digitOffset_succ (p N : ℕ) :
    digitOffset p (N + 1) =
      digitOffset p N + (2 : ℤ) ^ (3 * p - 1) * (2 : ℤ) ^ (3 * p * N) := by
  unfold digitOffset
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

end Work.KronP

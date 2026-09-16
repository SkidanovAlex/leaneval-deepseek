import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# Scaling the "lowbit" iteration by a power of two

For a natural number `n`, the *lowbit* `n - (n &&& (n - 1))` is the largest power of two
dividing `n` (written purely with bitwise operations).  The step map
`step n = n + (n - (n &&& (n - 1)))` therefore rounds `n` up to the next multiple of twice
its lowbit.

The main result `step_iter_two_pow_mul` records that this iteration commutes with scaling by a
power of two: `step^[i] (2 ^ a * z) = 2 ^ a * step^[i] z`.

The proof goes through the single bitwise identity `lowbit (2 * n) = 2 * lowbit n`
(`dyadicLowbit_two_mul`), from which scaling follows by induction on the exponent
(`dyadicLowbit_mul_two_pow`), then by induction on the iteration count.
-/

namespace Commons.Data.Nat

/-- The *lowbit* of `n`: the largest power of two dividing `n` (with `lowbit 0 = 0`),
expressed with bitwise operations as `n - (n &&& (n - 1))`. -/
def dyadicLowbit (n : ℕ) : ℕ := n - (n &&& (n - 1))

/-- The lowbit of an even number is twice the lowbit: `lowbit (2 * n) = 2 * lowbit n`. -/
lemma dyadicLowbit_two_mul (n : ℕ) : dyadicLowbit (2 * n) = 2 * dyadicLowbit n := by
  rcases n with _ | n
  · simp [dyadicLowbit]
  · -- `2 * (n + 1) = bit false (n + 1)` and `2 * (n + 1) - 1 = bit true n`
    have hsub : 2 * (n + 1) - 1 = Nat.bit true n := by
      rw [Nat.bit_true]
      change 2 * (n + 1) - 1 = 2 * n + 1
      omega
    have hbit : 2 * (n + 1) = Nat.bit false (n + 1) := by rw [Nat.bit_false]
    unfold dyadicLowbit
    rw [hsub, hbit, Nat.land_bit]
    simp only [Bool.false_and, Nat.bit_false]
    rw [← Nat.mul_sub_left_distrib, Nat.succ_sub_one]

/-- Scaling by a power of two scales the lowbit: `lowbit (2 ^ a * z) = 2 ^ a * lowbit z`. -/
lemma dyadicLowbit_mul_two_pow (a z : ℕ) : dyadicLowbit (2 ^ a * z) = 2 ^ a * dyadicLowbit z := by
  induction a generalizing z with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, mul_assoc, ih, dyadicLowbit_two_mul, mul_assoc]

/-- The step map `n ↦ n + lowbit n` commutes with scaling by a power of two. -/
lemma stepIter_mul_two_pow (a z : ℕ) :
    (2 ^ a * z) + ((2 ^ a * z) - ((2 ^ a * z) &&& (2 ^ a * z - 1))) =
      2 ^ a * (z + (z - (z &&& (z - 1)))) := by
  have h : (2 ^ a * z) - ((2 ^ a * z) &&& (2 ^ a * z - 1)) =
      2 ^ a * (z - (z &&& (z - 1))) := dyadicLowbit_mul_two_pow a z
  rw [h, Nat.mul_add]

theorem step_iter_two_pow_mul (a z i : ℕ) :
    Nat.iterate (fun n : ℕ => n + (n - (n &&& (n - 1)))) i (2 ^ a * z) =
      2 ^ a * Nat.iterate (fun n : ℕ => n + (n - (n &&& (n - 1)))) i z := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, stepIter_mul_two_pow]

end Commons.Data.Nat
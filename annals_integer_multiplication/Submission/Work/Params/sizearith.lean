import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.defs

/-!
# Elementary `Nat.size` / `vsz` arithmetic

Mathlib has `Nat.size_le`, `Nat.size_le_size`, `Nat.size_pow` but no monotonicity of `Nat.size`
under sums and products; these are the few facts the `Params` program needs when bounding the
`vsz` of the intermediate values on the stack.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

theorem szMul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le]
  have ha : a < 2 ^ a.size := Nat.size_le.mp le_rfl
  have hb : b < 2 ^ b.size := Nat.size_le.mp le_rfl
  calc a * b < 2 ^ a.size * 2 ^ b.size := by
        nlinarith [ha, hb, Nat.two_pow_pos a.size, Nat.two_pow_pos b.size]
    _ = 2 ^ (a.size + b.size) := (pow_add 2 a.size b.size).symm

theorem szAdd_le (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le]
  have ha : a < 2 ^ max a.size b.size :=
    lt_of_lt_of_le (Nat.size_le.mp le_rfl) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hb : b < 2 ^ max a.size b.size :=
    lt_of_lt_of_le (Nat.size_le.mp le_rfl) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  calc a + b < 2 ^ max a.size b.size + 2 ^ max a.size b.size := Nat.add_lt_add ha hb
    _ = 2 ^ (max a.size b.size + 1) := by rw [pow_succ]; ring

theorem szSub_le (a b : ℕ) : (a - b).size ≤ a.size :=
  Nat.size_le_size (Nat.sub_le a b)

theorem szOfPow {m k : ℕ} (h : m ≤ 2 ^ k) : m.size ≤ k + 1 := by
  rw [Nat.size_le]
  calc m ≤ 2 ^ k := h
    _ < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem szLe_of_le {m M : ℕ} (h : m ≤ M) : m.size ≤ M.size := Nat.size_le_size h

/-- `vsz` of a nonnegative integer value, in terms of the underlying natural. -/
theorem vsz_int_le {m B : ℕ} (h : m.size ≤ B) : vsz (Val.int (m : ℤ)) ≤ B + 2 := by
  rw [Work.Main.vsz_int, isz, Int.natAbs_natCast]
  omega

theorem vsz_int_neg_le {m B : ℕ} (h : m.size ≤ B) : vsz (Val.int (-(m : ℤ))) ≤ B + 2 := by
  rw [Work.Main.vsz_int, isz, Int.natAbs_neg, Int.natAbs_natCast]
  omega

/-- The value `-1`. -/
theorem vsz_int_neg_one : vsz (Val.int (-1 : ℤ)) = 3 := by
  rw [Work.Main.vsz_int, isz]
  norm_num

theorem vsz_int_one : vsz (Val.int (1 : ℤ)) = 3 := by
  rw [Work.Main.vsz_int, isz]
  norm_num

theorem szDiv_le (a b : ℕ) : (a / b).size ≤ a.size :=
  Nat.size_le_size (Nat.div_le_self a b)


theorem vszV {m B V : ℕ} (h : m.size ≤ B) (hBV : B + 2 ≤ V) : vsz (Val.int (m : ℤ)) ≤ V := by
  have := vsz_int_le h; omega

theorem vszVneg {m B V : ℕ} (h : m.size ≤ B) (hBV : B + 2 ≤ V) :
    vsz (Val.int (-(m : ℤ))) ≤ V := by
  have := vsz_int_neg_le h; omega

theorem iszV {m B W : ℕ} (h : m.size ≤ B) (hBW : B + 2 ≤ W) : isz ((m : ℤ)) ≤ W := by
  rw [HvdH.isz, Int.natAbs_natCast]; omega

theorem iszVneg {m B W : ℕ} (h : m.size ≤ B) (hBW : B + 2 ≤ W) : isz (-(m : ℤ)) ≤ W := by
  rw [HvdH.isz, Int.natAbs_neg, Int.natAbs_natCast]; omega

theorem szAdd_le2 {a b B : ℕ} (ha : a.size ≤ B) (hb : b.size ≤ B) : (a + b).size ≤ B + 1 := by
  have h := szAdd_le a b
  have h2 : max a.size b.size ≤ B := max_le ha hb
  omega

end Work.Params


import Mathlib
import Submission.Work.IntLib.Basic

/-!
# `ofBits` of `take`/`drop` of `Nat.bits`

Reading the low `k` bits of `n` recovers `n % 2 ^ k`, and reading the remaining
high bits (shifted down) recovers `n / 2 ^ k`.
-/

set_option autoImplicit false

namespace Work.IntLib

/-- `ofBits` inverts the canonical binary expansion `n.bits`. -/
theorem ofBits_bits_eq (n : ℕ) : ofBits n.bits = n := by
  rw [ofBits_eq_ofDigits, bits_map_toNat, Nat.ofDigits_digits]

theorem ofBits_take_drop_bits (n k : ℕ) :
    Work.IntLib.ofBits ((n.bits).take k) = n % 2 ^ k ∧
      Work.IntLib.ofBits ((n.bits).drop k) = n / 2 ^ k := by
  have hbits : ofBits n.bits = n := ofBits_bits_eq n
  have hsplit : ofBits n.bits = ofBits (n.bits.take k) + 2 ^ k * ofBits (n.bits.drop k) :=
    ofBits_take_drop n.bits k
  have hlt : ofBits (n.bits.take k) < 2 ^ k := by
    have h := ofBits_lt_two_pow (n.bits.take k)
    rw [List.length_take] at h
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (Nat.min_le_left _ _))
  constructor
  · conv_rhs => rw [← hbits, hsplit]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · conv_rhs => rw [← hbits, hsplit]
    rw [Nat.add_mul_div_left _ _ (pow_pos (by norm_num) k), Nat.div_eq_of_lt hlt, zero_add]

end Work.IntLib

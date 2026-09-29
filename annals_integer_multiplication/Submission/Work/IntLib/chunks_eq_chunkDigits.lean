import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBitsAPI

/-!
# `HvdH.chunks x b N` read off the bit encoding of `x`

`HvdH.chunks x b N` is the list of the `N` base-`2^b` digits of `x`, least significant first:
`(chunks x b N)[j] = x / 2^(b*j) % 2^b`.

The `chunk` word reads those digits off the *canonical bit encoding* `x.bits` (least significant
bit first) instead: it cuts the stream after `b*j` bits and takes the next `b` of them, i.e. it
produces `ofBits ((x.bits.drop (b*j)).take b)`.

This file identifies the two descriptions, so that the program-level specification of the `chunk`
word (phrased with `chunkDigits`) can be restated with the mathematical `HvdH.chunks`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- Reading only the low `b` bits of an arbitrary bit list: the remaining high bits contribute a
multiple of `2^b`, so they disappear modulo `2^b`. -/
theorem ofBits_take_mod (xs : List Bool) (b : ℕ) :
    ofBits (xs.take b) = ofBits xs % 2 ^ b := by
  have hsplit : ofBits xs = ofBits (xs.take b) + 2 ^ b * ofBits (xs.drop b) :=
    ofBits_take_drop xs b
  have hlt : ofBits (xs.take b) < 2 ^ b := by
    have h := ofBits_lt_two_pow (xs.take b)
    rw [List.length_take] at h
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (Nat.min_le_left _ _))
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The `j`-th base-`2^b` digit of `x`, as read off the bit stream `x.bits`, is the `j`-th entry
of `HvdH.chunks x b N`: cutting `b*j` low bits and taking the next `b` of them. -/
theorem chunkDigit_eq_chunks_getD (x b j : ℕ) :
    ofBits ((x.bits.drop (b * j)).take b) = x / 2 ^ (b * j) % 2 ^ b := by
  rw [ofBits_take_mod, (ofBits_take_drop_bits x (b * j)).2]

/-- The digits read off the canonical bit encoding of `x` are the mathematical base-`2^b`
digits recorded in `HvdH.chunks`. -/
theorem chunks_eq_chunkDigits (x b N : ℕ) :
    HvdH.chunks x b N = Work.IntLib.chunkDigits x.bits b N := by
  unfold HvdH.chunks Work.IntLib.chunkDigits
  apply List.map_congr_left
  intro j _
  exact (chunkDigit_eq_chunks_getD x b j).symm

end Work.IntLib

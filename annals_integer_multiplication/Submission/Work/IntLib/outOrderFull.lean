import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.range_blk_enc
import Submission.Work.IntLib.chunks_eq_chunkDigits

/-!
# The push order of the `chunk` word at the end of its loop is the encoding of `chunks x b N`

The `chunk` word of §2.1 reads the canonical bit stream `x.bits` of `x` (least significant bit
first, padded with zeros to `b*N` positions via `pbits`) and, for every group of `b` bits, pushes
`cons`, `pos`, the bits of the digit (low to high) and `iend`, finally pushing `nil`.  `outOrder ps
b k` is the push order after `k` bit positions; at `k = b*N` the loop has completed exactly `N`
groups and the push order (read from the stack bottom, hence the extra `nil` at the end) is the
encoding of the value `intList (chunks x b N)`.

The two combinatorial facts are
* `outOrder_mul`: at a multiple `b*N` of `b` the definition collapses to the `flatMap` of the
  per-group blocks over `List.range N` (here `1 ≤ b` is used, for `(b*N)/b = N` and `(b*N)%b = 0`);
* `flatMap_blk_pbits_enc`: that `flatMap`, followed by `nil`, is `Val.enc (intList (chunks x b N))`
  — the statement `range_blk_enc` of the sibling file with its (unused) bound `x < 2^(b*N)` dropped,
  and with `chunkDigits x.bits b N` replaced by the mathematical `HvdH.chunks x b N`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- At a multiple of `b` the clause of `outOrder` describing the group in progress is vacuous. -/
theorem outOrder_mul (ps : List Bool) (b N : ℕ) (hb : 1 ≤ b) :
    outOrder ps b (b * N) = List.flatMap (blk ps b) (List.range N) := by
  have hb0 : 0 < b := hb
  have h1 : (b * N) / b = N := Nat.mul_div_right N hb0
  have h2 : (b * N) % b = 0 := Nat.mul_mod_right b N
  simp [outOrder, h1, h2]

/-- The `N` per-group blocks pushed for the zero-padded bit stream of `x` encode the integer list
of the base-`2^b` digits of `x`.  No bound on `x` is needed: the padding is only used to make the
bit stream long enough, and cutting it at positions `b*j … b*j+b-1` reads the `j`-th digit of `x`
in all cases. -/
theorem flatMap_blk_pbits_enc (x b N : ℕ) :
    List.flatMap (blk (pbits x b N) b) (List.range N) ++ [Glyph.nil]
      = Val.enc (intList (chunks x b N)) := by
  have hmain : List.flatMap (blk (pbits x b N) b) (List.range N)
      = List.flatMap
          (fun j => Glyph.cons :: (Val.int ((ofBits ((x.bits.drop (b * j)).take b)) : ℤ)).enc)
          (List.range N) := by
    apply List.flatMap_congr
    intro j _
    exact blk_eq_enc x b N j
  rw [hmain, enc_intList_flatMap, chunks_eq_chunkDigits]
  congr 1
  exact (flatMap_map (fun d : ℕ => Glyph.cons :: (Val.int (d : ℤ)).enc)
    (fun j => ofBits ((x.bits.drop (b * j)).take b)) (List.range N)).symm

theorem outOrderFull (x b N : ℕ) (hb : 1 ≤ b) :
    Work.IntLib.outOrder (Work.IntLib.pbits x b N) b (b * N) ++ [HvdH.Glyph.nil]
      = HvdH.Val.enc (HvdH.intList (HvdH.chunks x b N)) := by
  rw [outOrder_mul (pbits x b N) b N hb]
  exact flatMap_blk_pbits_enc x b N

end Work.IntLib

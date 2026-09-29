import Mathlib
import Submission.Work.IntLib.stripFalses_map_bit
import Submission.Work.IntLib.padBitsAPI
import Submission.Work.IntLib.encodeNatBridge

namespace Work.IntLib

open HvdH

/-- Dropping the leading `bit false` glyphs after reversing a bit list is the same operation as
deleting the trailing zero bits (`MulS.stripHigh`), read through `List.map Glyph.bit`. -/
theorem dropWhile_map_bit_rev (l : List Bool) :
    (l.map HvdH.Glyph.bit).dropWhile (fun g => g = HvdH.Glyph.bit false)
      = (l.dropWhile (fun b : Bool => !b)).map HvdH.Glyph.bit := by
  have hp : ((fun g : HvdH.Glyph => decide (g = HvdH.Glyph.bit false)) ∘ HvdH.Glyph.bit)
      = (fun b : Bool => !b) := by
    funext b; cases b <;> rfl
  rw [List.dropWhile_map, hp]

/-- Dropping the leading `bit false` glyphs of the reverse of a bit list is the same as reversing
the canonicalisation `MulS.stripHigh` of that list. -/
theorem dropWhile_map_bit_rev_eq (l : List Bool) :
    ((l.reverse).map HvdH.Glyph.bit).dropWhile (fun g => g = HvdH.Glyph.bit false)
      = ((Work.IntLib.MulS.stripHigh l).map HvdH.Glyph.bit).reverse := by
  rw [dropWhile_map_bit_rev]
  have hstrip : l.reverse.dropWhile (fun b : Bool => !b)
      = (Work.IntLib.MulS.stripHigh l).reverse := by
    rw [Work.IntLib.MulS.stripHigh, List.reverse_reverse]
  rw [hstrip, List.map_reverse]

theorem dropWhile_rev_padBits_bits (n L : ℕ) (hn : n < 2 ^ L) :
    ((Work.IntLib.bitsG ((Work.IntLib.padBits n L).reverse)).dropWhile
        (fun g => g = HvdH.Glyph.bit false))
      = (Work.IntLib.bitsG (Computability.encodeNat n)).reverse := by
  simp only [Work.IntLib.bitsG]
  rw [dropWhile_map_bit_rev_eq, Work.IntLib.MulS.stripHigh_eq_bits,
      Work.IntLib.ofBits_padBits, Nat.mod_eq_of_lt hn, Work.IntLib.encodeNat_eq_bits]

end Work.IntLib

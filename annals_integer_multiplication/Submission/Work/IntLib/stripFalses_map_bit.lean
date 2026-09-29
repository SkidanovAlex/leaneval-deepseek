import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.mulSArith

namespace Work.IntLib

/-- `stripFalses` deletes the trailing `bit false` glyphs of `l.map Glyph.bit`, which corresponds
exactly to deleting the high-order (trailing) zero bits of the bit list `l`, i.e. to the canonical
form `MulS.stripHigh l`, read as glyphs. -/
theorem stripFalses_map_bit_aux (l : List Bool) :
    Work.IntLib.stripFalses (l.map HvdH.Glyph.bit) =
      (MulS.stripHigh l).map HvdH.Glyph.bit := by
  rw [stripFalses, MulS.stripHigh, ← List.map_reverse, List.dropWhile_map]
  rw [show (fun g : HvdH.Glyph => decide (g = HvdH.Glyph.bit false)) ∘ HvdH.Glyph.bit
        = (fun b : Bool => !b) from by
      funext b; cases b <;> simp]
  exact List.map_reverse.symm

/-- Stripping the trailing `bit false` glyphs of the glyph image of a bit list is the same as
canonicalising the bit list (deleting its high-order zeros) and then taking the glyph image. -/
theorem stripFalses_map_bit (l : List Bool) :
    Work.IntLib.stripFalses (l.map HvdH.Glyph.bit) =
      ((Work.IntLib.ofBits l).bits).map HvdH.Glyph.bit := by
  rw [← MulS.stripHigh_eq_bits l]
  exact stripFalses_map_bit_aux l

end Work.IntLib

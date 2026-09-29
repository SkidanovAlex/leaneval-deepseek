import Mathlib
import Submission.Work.IntLib.chunkDefs

namespace Work.IntLib

/-- `List.dropWhile` stops at an element failing the predicate, so appending such an element
followed by an arbitrary list only changes what precedes it. -/
lemma dropWhile_append_cons_of_not {α : Type*} (p : α → Bool) {h : α} (hh : p h = false)
    (l m : List α) : (l ++ h :: m).dropWhile p = l.dropWhile p ++ h :: m := by
  induction l with
  | nil => simp [hh]
  | cons a t ih =>
    rw [List.cons_append]
    by_cases ha : p a
    · rw [List.dropWhile_cons_of_pos ha, ih, List.dropWhile_cons_of_pos ha]
    · rw [List.dropWhile_cons_of_neg ha, List.dropWhile_cons_of_neg ha, List.cons_append]

/-- `stripFalses` only deletes the *trailing* run of `bit false` glyphs, so an element which is not
`bit false` blocks the deletion: nothing to its left is affected, and the part to its right is
stripped independently. -/
theorem stripFalses_append_cons {X G : List HvdH.Glyph} {h : HvdH.Glyph} (hh : h ≠ HvdH.Glyph.bit false) : Work.IntLib.stripFalses (X ++ h :: G) = X ++ h :: Work.IntLib.stripFalses G := by
  have hh' : (fun g : HvdH.Glyph => decide (g = HvdH.Glyph.bit false)) h = false := by simp [hh]
  simp only [Work.IntLib.stripFalses, List.reverse_cons, List.reverse_append]
  rw [List.append_assoc, List.singleton_append]
  rw [dropWhile_append_cons_of_not (fun g : HvdH.Glyph => decide (g = HvdH.Glyph.bit false)) hh'
        G.reverse X.reverse]
  simp

end Work.IntLib

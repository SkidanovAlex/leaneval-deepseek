import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.outOrderFull

/-!
# Length of the push order of the `chunk` word at the end of its loop

At `k = b*N` the push order `outOrder (pbits x b N) b (b*N)` is the `flatMap` of the `N` per-group
blocks `blk` (`outOrder_mul`).  Each block consists of the two glyphs `cons`, `pos`, the canonical
bits of the digit (at most `b` of them, since only `b` bits of the stream are read) and `iend`:
length at most `b + 3`.  Summing over the `N` groups gives the bound `N * (b + 3)` used by the
`chunk` word's cost estimate (the cost is proportional to the number of glyphs pushed).

The hypothesis `x < 2 ^ (b*N)` is not needed for the counting argument; it is part of the interface
of the `chunk` word, where it makes `chunks x b N` the base-`2^b` digit expansion of `x`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- `stripFalses` deletes trailing glyphs, so it never lengthens a list. -/
theorem stripFalses_length_le (l : List Glyph) : (stripFalses l).length ≤ l.length := by
  have h := List.length_dropWhile_le (fun g : Glyph => g = Glyph.bit false) l.reverse
  simpa [stripFalses] using h

/-- A complete group block has at most `b + 3` glyphs. -/
theorem blk_length_le (ps : List Bool) (b j : ℕ) : (blk ps b j).length ≤ b + 3 := by
  have h1 : (((ps.drop (b * j)).take b).map Glyph.bit).length ≤ b := by
    rw [List.length_map, List.length_take]
    exact Nat.min_le_left _ _
  have h2 := stripFalses_length_le (((ps.drop (b * j)).take b).map Glyph.bit)
  simp only [blk, List.length_append, List.length_cons, List.length_nil]
  omega

/-- A `flatMap` of `N` blocks of length at most `b + 3` has length at most `N * (b + 3)`. -/
theorem length_flatMap_range_le (f : ℕ → List Glyph) (b N : ℕ)
    (h : ∀ j, (f j).length ≤ b + 3) :
    (List.flatMap f (List.range N)).length ≤ N * (b + 3) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append]
    have hN := h N
    have hnil : (List.flatMap f [N]).length = (f N).length := by simp
    rw [hnil]
    calc (List.flatMap f (List.range N)).length + (f N).length
        ≤ N * (b + 3) + (b + 3) := Nat.add_le_add ih hN
      _ = (N + 1) * (b + 3) := by ring

theorem outOrderLen (x b N : ℕ) (hb : 1 ≤ b) (hx : x < 2 ^ (b * N)) :
    (Work.IntLib.outOrder (Work.IntLib.pbits x b N) b (b * N)).length ≤ N * (b + 3) := by
  rw [outOrder_mul (pbits x b N) b N hb]
  exact length_flatMap_range_le (blk (pbits x b N) b) b N (fun j => blk_length_le _ _ _)

end Work.IntLib

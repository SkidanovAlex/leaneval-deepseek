import Mathlib
import Submission.Work.SG.SGRepDefs

/-!
# The block accessor `RC.blk` reads three consecutive coordinates

`RC.blk v g` is the `g`-th block of three of the flat vector `v` (`Data.blocks v`), with `0`
padding outside the block list.  Whenever the block is *complete* -- `3 * (g + 1) ≤ v.length` --
its `c`-th coordinate is exactly the coordinate `3 * g + c` of `v`.

The proof factors through the list identity `v.drop (3 * g)`, whose blocks are precisely the
blocks of `v` with the first `g` of them removed.
-/

namespace Work.SG

namespace RC

/-- Reading a `getD` at `m` in a dropped list is reading `getD` at `n + m` in the original
list (for an arbitrary default). -/
theorem blk_getD_drop {α : Type*} (l : List α) (n m : ℕ) (d : α) :
    (l.drop n).getD m d = l.getD (n + m) d := by
  induction l generalizing n with
  | nil => cases n <;> simp
  | cons a t ih =>
      cases n with
      | zero => simp
      | succ n => rw [List.drop_succ_cons, Nat.succ_add, List.getD_cons_succ, ih]

/-- Dropping one block is dropping the first three coordinates. -/
theorem blk_blocks_drop3 (l : List ℤ) :
    Data.blocks (l.drop 3) = (Data.blocks l).drop 1 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> simp [Data.blocks]

/-- Dropping `k` blocks is dropping the first `3 * k` coordinates. -/
theorem blk_blocks_drop (v : List ℤ) (k : ℕ) :
    Data.blocks (v.drop (3 * k)) = (Data.blocks v).drop k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, ← List.drop_drop, blk_blocks_drop3, ih, List.drop_drop]

/-- The first block of a vector holding at least one complete block. -/
theorem blk_blocks_getD_zero (w : List ℤ) (h : 3 ≤ w.length) :
    (Data.blocks w).getD 0 Data.V3.zero = ⟨w.getD 0 0, w.getD 1 0, w.getD 2 0⟩ := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp_all [Data.blocks]

/-- The `g`-th block of a flat vector is the triple of coordinates `3 * g`, `3 * g + 1`,
`3 * g + 2`. -/
theorem blk_getD_three (v : List ℤ) (g : ℕ) (h : 3 * (g + 1) ≤ v.length) :
    (Data.blocks v).getD g Data.V3.zero =
      ⟨v.getD (3 * g) 0, v.getD (3 * g + 1) 0, v.getD (3 * g + 2) 0⟩ := by
  have hw : 3 ≤ (v.drop (3 * g)).length := by rw [List.length_drop]; omega
  calc (Data.blocks v).getD g Data.V3.zero
      = ((Data.blocks v).drop g).getD 0 Data.V3.zero :=
        (blk_getD_drop (Data.blocks v) g 0 Data.V3.zero).symm
    _ = (Data.blocks (v.drop (3 * g))).getD 0 Data.V3.zero := by rw [blk_blocks_drop]
    _ = ⟨(v.drop (3 * g)).getD 0 0, (v.drop (3 * g)).getD 1 0,
          (v.drop (3 * g)).getD 2 0⟩ := blk_blocks_getD_zero _ hw
    _ = ⟨v.getD (3 * g) 0, v.getD (3 * g + 1) 0, v.getD (3 * g + 2) 0⟩ := by
        rw [blk_getD_drop, blk_getD_drop, blk_getD_drop, Nat.add_zero]

end RC

theorem RepCoh_blk (v : List ℤ) (g : ℕ) (c : Fin 3) (h : 3 * (g + 1) ≤ v.length) :
    (Work.SG.RC.blk v g).toFun c = v.getD (3 * g + c.val) 0 := by
  rw [Work.SG.RC.blk, RC.blk_getD_three v g h]
  fin_cases c <;> simp [Data.V3.toFun]

end Work.SG

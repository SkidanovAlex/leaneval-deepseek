import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Checking a sparse operator equality a block of columns at a time

`SOp.eqb A B` compares all the columns of `A` and `B`.  For a large operator the single kernel
`decide` of that comparison is expensive in memory; `eqbCols A B lo len` compares only the
columns `lo, …, lo + len - 1`, so that the comparison can be split into several small `decide`s,
and `eqb_of_img` reassembles them.
-/

namespace Work.Certificates.SOp

variable {n m : ℕ}

/-- The column comparison of `SOp.eqb`, restricted to the columns `lo ≤ j < lo + len`. -/
def eqbCols (A B : SOp n m) (lo len : ℕ) : Bool :=
  (List.range' lo len).all
    (fun j => if h : j < m then (A.img ⟨j, h⟩).eqb (B.img ⟨j, h⟩) else true)

/-- A passing block check gives the column comparison for every column of the block. -/
theorem img_eqb_of_eqbCols {A B : SOp n m} {lo len : ℕ} (h : eqbCols A B lo len = true)
    (j : Fin m) (h1 : lo ≤ j.val) (h2 : j.val < lo + len) : (A.img j).eqb (B.img j) = true := by
  have hj := List.all_eq_true.mp h j.val (List.mem_range'_1.mpr ⟨h1, h2⟩)
  simpa only [j.isLt, dite_true] using hj

/-- The last block of columns: it is enough that the block reaches the column count. -/
theorem img_eqb_of_eqbCols_last {A B : SOp n m} {lo len : ℕ} (h : eqbCols A B lo len = true)
    (hm : m ≤ lo + len) (j : Fin m) (h1 : lo ≤ j.val) : (A.img j).eqb (B.img j) = true :=
  img_eqb_of_eqbCols h j h1 (lt_of_lt_of_le j.isLt hm)

/-- `SOp.eqb` from the comparison of every column. -/
theorem eqb_of_img {A B : SOp n m} (h : ∀ j, (A.img j).eqb (B.img j) = true) :
    A.eqb B = true :=
  List.all_eq_true.mpr fun j _ => h j

end Work.Certificates.SOp

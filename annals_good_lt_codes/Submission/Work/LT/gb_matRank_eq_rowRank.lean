import Mathlib
import Submission.Work.LT.good_base_defs

/-!
# Column rank = row rank (matrices over `𝔽₂`)

`GB.matRank x` is the dimension of the span of the columns of `x`, while `GB.frk (GB.rowSpan x)`
is the dimension of the span of its rows; the two agree.

The proof reads `x` as a genuine `Matrix (Fin D) (Fin D) (ZMod 2)`.  Under that identification the
columns of `x` are exactly the columns of the matrix and the rows of `x` exactly its rows, so both
sides are `Matrix.rank` computed in two ways: `Matrix.rank_eq_finrank_span_cols` for the columns
and `Matrix.rank_eq_finrank_span_row` (= `Matrix.rank_transpose`) for the rows.
-/

namespace Work.LT

namespace GB

variable {D : ℕ}

/-- The matrix associated with a function on `Fin D × Fin D`. -/
private def toMat (x : Fin D × Fin D → ZMod 2) : Matrix (Fin D) (Fin D) (ZMod 2) :=
  fun i j => x (i, j)

/-- `GB.colSpan` is the span of the columns of the associated matrix. -/
private lemma colSpan_eq (x : Fin D × Fin D → ZMod 2) :
    colSpan x = Submodule.span (ZMod 2) (Set.range (toMat x).col) := by
  unfold colSpan
  congr 1

/-- `GB.rowSpan` is the span of the rows of the associated matrix. -/
private lemma rowSpan_eq (x : Fin D × Fin D → ZMod 2) :
    rowSpan x = Submodule.span (ZMod 2) (Set.range (toMat x).row) := by
  unfold rowSpan
  congr 1

end GB

/-- The dimension of the column space of a matrix equals the dimension of its row space. -/
theorem gb_matRank_eq_rowRank {D : ℕ} (x : Fin D × Fin D → ZMod 2) :
    GB.matRank x = GB.frk (GB.rowSpan x) := by
  have h1 : GB.frk (GB.colSpan x) = (GB.toMat x).rank := by
    rw [GB.colSpan_eq, Matrix.rank_eq_finrank_span_cols]
    unfold GB.frk
    rfl
  have h2 : GB.frk (GB.rowSpan x) = (GB.toMat x).rank := by
    rw [GB.rowSpan_eq, Matrix.rank_eq_finrank_span_row]
    unfold GB.frk
    rfl
  exact h1.trans h2.symm

end Work.LT

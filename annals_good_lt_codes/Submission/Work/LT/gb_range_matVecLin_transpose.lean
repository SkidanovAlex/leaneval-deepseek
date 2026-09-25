import Mathlib
import Submission.Work.LT.gb_rank_defs

/-!
# The range of `v ↦ xᵀ v` is the row space of `x`

For a matrix `x : Fin D × Fin D → ZMod 2` the linear map `v ↦ xᵀ * v` (`GB.matVecLin` of the
transpose `GB.matTranspose x = fun ij => x (ij.2, ij.1)`) has range exactly the span of the rows
of `x` (`GB.rowSpan x`).

The reason is the standard identity `row x i = col (xᵀ) i`: the image of the `i`-th standard basis
vector `eᵢ` under `v ↦ xᵀ v` is the `i`-th row of `x`, and conversely `xᵀ * w = ∑ i, w i • row x i`
exhibits every element of the range as a linear combination of the rows.
-/

namespace Work.LT

namespace GB

variable {D : ℕ}

/-- The image of the `i`-th standard basis vector under `v ↦ xᵀ * v` is the `i`-th row of `x`. -/
private lemma matVec_matTranspose_single (x : Fin D × Fin D → ZMod 2) (i : Fin D) :
    matVec (matTranspose x) (Pi.single i 1) = row x i := by
  ext k
  simp only [matVec, matTranspose_apply, row]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `xᵀ * w` is the linear combination `∑ i, w i • (i-th row of x)`. -/
private lemma matVec_matTranspose_eq_sum (x : Fin D × Fin D → ZMod 2) (w : Fin D → ZMod 2) :
    matVec (matTranspose x) w = ∑ i, w i • row x i := by
  ext k
  simp only [matVec, matTranspose_apply, row, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Every row of `x` lies in the range of `v ↦ xᵀ * v`. -/
private lemma row_mem_range_matVecLin_matTranspose (x : Fin D × Fin D → ZMod 2) (i : Fin D) :
    row x i ∈ LinearMap.range (matVecLin (matTranspose x)) :=
  ⟨Pi.single i 1, by rw [matVecLin_apply, matVec_matTranspose_single]⟩

/-- The range of `v ↦ xᵀ * v` is contained in the row space of `x`. -/
private lemma range_matVecLin_matTranspose_le_rowSpan (x : Fin D × Fin D → ZMod 2) :
    LinearMap.range (matVecLin (matTranspose x)) ≤ rowSpan x := by
  rintro v ⟨w, rfl⟩
  rw [matVecLin_apply, matVec_matTranspose_eq_sum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (row_mem_rowSpan x i)

/-- The row space of `x` is contained in the range of `v ↦ xᵀ * v`. -/
private lemma rowSpan_le_range_matVecLin_matTranspose (x : Fin D × Fin D → ZMod 2) :
    rowSpan x ≤ LinearMap.range (matVecLin (matTranspose x)) :=
  rowSpan_le_iff.2 fun i => row_mem_range_matVecLin_matTranspose x i

end GB

/-- (file `Submission/Work/LT/gb_range_matVecLin_transpose.lean`, inside `namespace Work.LT` / `namespace GB`, importing `Submission.Work.LT.gb_rank_defs`) The range of `v ↦ xᵀ * v` (where `GB.matTranspose x = fun ij => x (ij.2, ij.1)`) is the row space of `x`, i.e. the span of the rows `GB.row x i = fun j => x (i,j)`. -/
lemma gb_range_matVecLin_transpose {D : ℕ} (x : Fin D × Fin D → ZMod 2) :
    LinearMap.range (GB.matVecLin (GB.matTranspose x)) = GB.rowSpan x :=
  le_antisymm (GB.range_matVecLin_matTranspose_le_rowSpan x)
    (GB.rowSpan_le_range_matVecLin_matTranspose x)

end Work.LT

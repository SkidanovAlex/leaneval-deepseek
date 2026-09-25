import Mathlib
import Submission.Work.LT.gb_rank_defs

/-!
# The range of `v ↦ x * v` is the column space of `x`

`GB.matVecLin x` is the linear map `v ↦ GB.matVec x v` sending `v` to the column
combination `fun i => ∑ j, x (i,j) * v j`. Since the `j`-th column
`GB.col x j = fun i => x (i,j)` is the image of the `j`-th standard basis vector
`Pi.single j 1`, and conversely every matrix-vector product is the column combination
`∑ j, v j • GB.col x j`, the range of `GB.matVecLin x` is exactly `GB.colSpan x`.
-/

namespace Work.LT

namespace GB

variable {D : ℕ}

/-- The `j`-th column of `x` is the image of the `j`-th standard basis vector under
`v ↦ x * v`. -/
lemma col_eq_matVecLin_single (x : Fin D × Fin D → ZMod 2) (j : Fin D) :
    col x j = matVecLin x (Pi.single j 1) := by
  funext i
  simp only [matVecLin_apply, matVec, col, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [hk]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The matrix-vector product `x * v` is the linear combination of the columns of `x`
with coefficients `v j`. -/
lemma matVec_eq_sum_smul_col (x : Fin D × Fin D → ZMod 2) (v : Fin D → ZMod 2) :
    matVec x v = ∑ j, v j • col x j := by
  funext i
  simp only [matVec, col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

end GB

/-- (file `Submission/Work/LT/gb_range_matVecLin.lean`, declaring this inside `namespace Work.LT` / `namespace GB`, importing `Submission.Work.LT.gb_rank_defs`) The range of the linear map `v ↦ x * v` (namely `GB.matVecLin x`, where `GB.matVec x v = fun i => ∑ j, x (i,j) * v j`) is the column space of `x`, i.e. the span of the columns `GB.col x j = fun i => x (i,j)`. -/
lemma gb_range_matVecLin {D : ℕ} (x : Fin D × Fin D → ZMod 2) :
    LinearMap.range (GB.matVecLin x) = GB.colSpan x := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [GB.matVecLin_apply, GB.matVec_eq_sum_smul_col]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  · rw [GB.colSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single j 1, (GB.col_eq_matVecLin_single x j).symm⟩

end Work.LT

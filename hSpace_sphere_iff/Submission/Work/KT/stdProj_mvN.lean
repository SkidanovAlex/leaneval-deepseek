import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.FiberUtil

namespace Work.KT

open Matrix

/-! ## The standard projection `diag(1_m, 0_m)` is MvN to `1_m`

`stdProj R m` is the block matrix `diag(1_m, 0_m)` of size `m + m`.  Writing it over the sum
index type `Fin m ⊕ Fin m` it is `stdProjBlocks R m = fromBlocks 1 0 0 0`, and the two
rectangular matrices

* `blockIncl R m : Matrix (Fin m) (Fin m ⊕ Fin m)` — the inclusion of the first summand
  (`R^m → R^m ⊕ R^m`), and
* `blockProj R m : Matrix (Fin m ⊕ Fin m) (Fin m)` — the projection onto the first summand,

satisfy `blockProj * blockIncl = stdProjBlocks` and `blockIncl * blockProj = 1`.  Reindexing the
`Fin m ⊕ Fin m` index type to `Fin (m + m)` along `finSumFinEquiv` (which is what `stdProj`
records) gives the two witnesses of the Murray–von Neumann equivalence.

The reductions above are proved with `submatrix_mul`: in both products of the *reindexed*
matrices the middle index type is `Fin (m + m)` and the middle reindexing map is the identity, so
`Matrix.submatrix_mul` applies and the whole verification is transported from the block form.
-/

variable {R : Type} [Ring R]

/-- `diag(1_m, 0_m)` as a matrix indexed by `Fin m ⊕ Fin m`. -/
private def stdProjBlocks (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R :=
  Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) R) 0 0 0

/-- The inclusion of the first summand `R^m → R^m ⊕ R^m`. -/
private def blockIncl (m : ℕ) : Matrix (Fin m) (Fin m ⊕ Fin m) R :=
  (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R).submatrix (fun i => Sum.inl i) id

/-- The projection onto the first summand `R^m ⊕ R^m → R^m`. -/
private def blockProj (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m) R :=
  (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R).submatrix id (fun i => Sum.inl i)

private lemma stdProj_eq_reindex (m : ℕ) :
    stdProj R m = Matrix.reindex finSumFinEquiv finSumFinEquiv (stdProjBlocks (R := R) m) := rfl

private lemma blockProj_mul_blockIncl (m : ℕ) :
    blockProj (R := R) m * blockIncl (R := R) m = stdProjBlocks (R := R) m := by
  ext s s'
  rw [Matrix.mul_apply]
  rcases s with i0 | i0
  · -- the sum localises at `i0`, and the remaining entry is the `(1,1)` block of `diag(1,0)`
    refine (Finset.sum_eq_single i0 ?_ ?_).trans ?_
    · intro i _ hi
      have hne : (Sum.inl i0 : Fin m ⊕ Fin m) ≠ Sum.inl i :=
        fun h => hi (Sum.inl_injective h).symm
      simp [blockProj, Matrix.submatrix_apply, hne]
    · intro h; exact absurd (Finset.mem_univ i0) h
    · rcases s' with i' | i' <;>
        simp [blockProj, blockIncl, stdProjBlocks, Matrix.submatrix_apply, Matrix.one_apply,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Sum.inl.injEq]
  · -- the whole `inr` row of `blockProj` vanishes
    rw [show stdProjBlocks (R := R) m (Sum.inr i0) s' = 0 by
        rcases s' with i' | i' <;>
          simp [stdProjBlocks, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hne : (Sum.inr i0 : Fin m ⊕ Fin m) ≠ Sum.inl i := Sum.inr_ne_inl
    simp [blockProj, Matrix.submatrix_apply, hne]

private lemma blockIncl_mul_blockProj (m : ℕ) :
    blockIncl (R := R) m * blockProj (R := R) m = 1 := by
  simp only [blockIncl, blockProj]
  rw [← Matrix.submatrix_mul (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R)
    (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) (fun i => Sum.inl i) id (fun i => Sum.inl i)
    Function.bijective_id]
  rw [mul_one]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply, Sum.inl.injEq]

/-- The standard projection `diag(1_m, 0_m)` is Murray–von Neumann equivalent to the identity of
size `m` (project onto the first block, include the first block). -/
theorem stdProj_mvN {R : Type} [Ring R] (m : ℕ) :
    Mat.MvN (⟨m + m, stdProj R m⟩ : Mat R) (Mat.one R m) := by
  unfold Mat.one
  refine ⟨(blockIncl (R := R) m).submatrix id finSumFinEquiv.symm,
    (blockProj (R := R) m).submatrix finSumFinEquiv.symm id, ?_, ?_⟩
  · rw [← Matrix.submatrix_mul (blockProj (R := R) m) (blockIncl (R := R) m)
      finSumFinEquiv.symm id finSumFinEquiv.symm Function.bijective_id, blockProj_mul_blockIncl,
      stdProj_eq_reindex, Matrix.reindex_apply]
  · rw [← Matrix.submatrix_mul (blockIncl (R := R) m) (blockProj (R := R) m) id
      finSumFinEquiv.symm id (Equiv.bijective _), blockIncl_mul_blockProj]
    exact Matrix.submatrix_id_id _

end Work.KT

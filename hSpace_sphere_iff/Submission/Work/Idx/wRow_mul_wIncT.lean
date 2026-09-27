import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenPsi

namespace Work.Idx

/-- **The coefficient row of the restricted pencil.**

`wRow n D c` is the block row `Matrix (Fin n) (Fin (D+1) × Fin n)` with block `k` equal to `c k`,
`wInc n d` is the block inclusion `Matrix (Fin (d+2) × Fin n) (Fin (d+1) × Fin n)` (the identity in
the first `d+1` blocks, zero in the last one).

Claim: `wRow n d b * Matrix.transpose (wInc n d)` is the block row of the `(d+2)`-block index whose
block `k` is `b k` for `k ≤ d` and `0` for `k = d+1`; i.e. it is `wRow n (d+1) (appSeq X b)` where
`appSeq` is the "append a zero coefficient" map of `Submission/Work/KT/Idx/WPen.lean`.  This is the
elementary index identity making the Fourier relation `Work.Idx.wRow_wPsi` of the *small* pencil
describe the coefficients of a `(d+2)`-block matrix, and it is used to show that the coefficient
row annihilates the pencil projection.

Proof: compute entries with `Matrix.mul_apply`, `Matrix.transpose_apply` and the definition of
`wInc`; the sum over `Fin (d+1) × Fin n` collapses to the single term at the index with the same
block and inner index (`Finset.sum_eq_single` + `Fin.ext`), which exists exactly when
`(q.1 : ℕ) < d + 1`, matching `appSeq X b q.1`. -/
theorem wRow_mul_wIncT {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    wRow n d b * Matrix.transpose (wInc (X := X) n d)
      = wRow n (d + 1) (Work.KT.Idx.appSeq X b) := by
  apply Matrix.ext
  intro c' p
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, wRow, wInc, Work.KT.Idx.appSeq]
  by_cases hp : (p.1 : ℕ) < d + 1
  · -- The index `p` lies in the retained blocks: the sum keeps exactly the term `q = (p.1, p.2)`.
    rw [dif_pos hp]
    refine (Finset.sum_eq_single (⟨(p.1 : ℕ), hp⟩, p.2) ?_ ?_).trans ?_
    · intro q _ hq
      rw [if_neg]
      · simp
      · intro h
        refine hq (Prod.ext ?_ ?_)
        · exact Fin.ext h.1.symm
        · exact h.2.symm
    · intro h; simp at h
    · simp
  · -- The index `p` lies in the appended block `d+1`: every term of the sum vanishes.
    rw [dif_neg hp]
    simp only [Matrix.zero_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    · simp
    · intro h
      have : (q.1 : ℕ) < d + 1 := q.1.isLt
      omega

end Work.Idx

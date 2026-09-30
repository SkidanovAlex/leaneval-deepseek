import Mathlib
import Submission.Work.BW.sieg2AdjDefs
import Submission.Work.BW.sumSqInnerMulK

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The diagonal of `PhiMat a * (PhiMat a)ᵀ`

`PhiMat a` is the matrix of the `ℝ`-linear map `Phi a` in the orthonormal basis
`stdOrthonormalBasis F` of the Euclidean mixed space.  Hence the `(p, p)` entry of
`PhiMat a * (PhiMat a)ᵀ` is the sum of squares of the entries of the `p`-th row of `PhiMat a`,
which is exactly the sum over `j` of the sums of squares of the entries of the matrix of
`mulK (a p.1 j)`.  By `Work.BW.sumSqInnerMulK` each of those per-`j` sums is
`(stdPlace p.2 (a p.1 j))²`.

The statement uses `stdPlace`, which is definitionally the same place map as `siegPlaceOf`.
-/

open NumberField

namespace Work.BW

theorem PhiMat_diag {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) (p : Fin M × NumberField.mixedEmbedding.index F) :
    ((Work.BW.PhiMat a) * (Work.BW.PhiMat a).transpose) p p =
      ∑ j : Fin N, (Work.BW.stdPlace p.2 (a p.1 j)) ^ 2 := by
  classical
  have hplace : ∀ q : NumberField.mixedEmbedding.index F,
      siegPlaceOf (F := F) q = stdPlace (F := F) q := by
    intro q
    rcases q with w | ⟨w, k⟩ <;> simp [siegPlaceOf, stdPlace]
  have hA : ∀ q : Fin N × NumberField.mixedEmbedding.index F,
      PhiMat a p q = inner ℝ
        (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F p.2)
        (mulK (a p.1 q.1)
          (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F q.2)) := by
    rintro ⟨j, s⟩
    simp only [PhiMat, Phi_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have h1 : ∀ q : Fin N × NumberField.mixedEmbedding.index F,
      PhiMat a p q * PhiMat a p q
        = (inner ℝ (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F p.2)
            (mulK (a p.1 q.1)
              (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F q.2))) ^ 2 := by
    intro q
    rw [hA q, sq]
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_congr rfl (fun q _ => h1 q)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sumSqInnerMulK (a p.1 j) p.2, hplace p.2]

end Work.BW

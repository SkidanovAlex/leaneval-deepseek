import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.siegBlockRow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sum of squares of one row of the matrix of `mulK`

Let `v = stdOrthonormalBasis F` be the orthonormal basis of the Euclidean mixed space
`KE F = mixedEmbedding.euclidean.mixedSpace F`.  For `α : F` and `ζ : index F`, the `ζ`-th row of
the matrix of the `ℝ`-linear map `mulK α` in this basis has sum of squares `(siegPlaceOf ζ α)²`:
this is the sharp "per place" arithmetic input of the Bombieri–Vaaler kernel-lattice bound.

The proof identifies the matrix entry with the corresponding entry of the matrix of
multiplication by `mixedEmbedding F α` in the basis `stdBasis F` (the two bases are intertwined by
the linear equivalence `toMixed F`), and then applies `Work.BW.sieg_block_row`.
-/

namespace Work.BW

open NumberField
open scoped Classical

/-- The `(ζ, η)` entry of the matrix of `mulK α` in the orthonormal basis equals the `(ζ, η)`
entry of the matrix of multiplication by `mixedEmbedding F α` in `stdBasis F`. -/
theorem inner_stdOrthonormalBasis_mulK {F : Type*} [Field F] [NumberField F] (α : F)
    (ζ η : NumberField.mixedEmbedding.index F) :
    inner ℝ ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F) ζ)
        (mulK α ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F) η))
      = ((NumberField.mixedEmbedding.stdBasis F).repr
          (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F η)) ζ := by
  set v := NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F with hv
  set V := NumberField.mixedEmbedding.stdBasis F with hV
  set e := NumberField.mixedEmbedding.euclidean.toMixed F with he
  have hmap : ∀ c, e (v c) = V c := by
    intro c
    have h := NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis_map_eq F
    have := congrArg (fun (b : Module.Basis (NumberField.mixedEmbedding.index F) ℝ
        (NumberField.mixedEmbedding.mixedSpace F)) => b c) h
    simpa [hv, hV, he] using this
  have hesymm : ∀ c, e.symm (V c) = v c :=
    fun c => by rw [← hmap c, ContinuousLinearEquiv.symm_apply_apply]
  have hmul : e (mulK α (v η)) = NumberField.mixedEmbedding F α * V η := by
    rw [mulK_apply, ContinuousLinearEquiv.apply_symm_apply, hmap η]
  have hexp : mulK α (v η) = e.symm (NumberField.mixedEmbedding F α * V η) := by
    rw [← hmul, ContinuousLinearEquiv.symm_apply_apply]
  have hrepr : (∑ c, (V.repr (NumberField.mixedEmbedding F α * V η)) c • V c)
      = NumberField.mixedEmbedding F α * V η := Module.Basis.sum_repr _ _
  have hsum : mulK α (v η) = ∑ c, (V.repr (NumberField.mixedEmbedding F α * V η)) c • v c := by
    rw [hexp]
    conv_lhs => rw [← hrepr]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [map_smul, hesymm c]
  rw [hsum]
  exact v.orthonormal.inner_right_fintype _ _

theorem sumSqInnerMulK {F : Type*} [Field F] [NumberField F] (α : F)
    (ζ : NumberField.mixedEmbedding.index F) :
    ∑ η : NumberField.mixedEmbedding.index F,
        (inner ℝ ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F) ζ)
          (Work.BW.mulK α ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F) η))) ^ 2
      = (Work.BW.siegPlaceOf ζ α) ^ 2 := by
  classical
  rw [Finset.sum_congr rfl (fun η _ => by rw [inner_stdOrthonormalBasis_mulK α ζ η])]
  rw [sieg_block_row α ζ]
  rw [NumberField.InfinitePlace.norm_embedding_eq]

end Work.BW

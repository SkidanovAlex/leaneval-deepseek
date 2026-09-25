import Mathlib
import Submission.Work.LT.gb_ext_defs

/-!
# `matRank (matExt A B u w x) ≤ matRank x`

For `u = opVec T` (the columns of an extension operator `T`) and arbitrary `w`, the
"extension" matrix `matExt A B u w x` is `U · x · Wᵀ` in matrix language, where
`U` has columns `u i` (`i ∈ A`) and `W` has columns `w j` (`j ∈ B`), and `x` is
restricted to the rows `A` and columns `B`.  Its rank cannot exceed the rank of `x`:
viewing `matExt` as the composite `U ∘ (x restricted to the columns `B`)`, the column
space of `matExt` is the image under the linear map `U` of a subspace of `colSpan x`,
and passing to the image of a linear map does not increase dimension.

Concretely, using only that `u = opVec T` (no property of `T` is needed), every column of
`matExt A B (opVec T) w x` is
`∑ j ∈ B, w j q • U (col x j) = U (∑ j ∈ B, w j q • col x j)`,
with `∑ j ∈ B, w j q • col x j ∈ colSpan x`.
-/

namespace Work.LT

theorem gb_matRank_matExt_le {D : ℕ} {C : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (A B : Finset (Fin D)) (T : GB.ExtOp C A) (w : Fin D → (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) :
    GB.matRank (GB.matExt A B (GB.opVec T) w x) ≤ GB.matRank x := by
  -- The linear map `U z = ∑ i ∈ A, opVec T i * z i`.
  let U : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) :=
    { toFun := fun z k => ∑ i ∈ A, GB.opVec T i k * z i
      map_add' := by
        intro z z'
        funext k
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c z
        funext k
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  have hU : ∀ z k, U z k = ∑ i ∈ A, GB.opVec T i k * z i := fun _ _ => rfl
  -- Every column of `matExt` lies in the image under `U` of `colSpan x`.
  have hle : GB.colSpan (GB.matExt A B (GB.opVec T) w x) ≤ (GB.colSpan x).map U := by
    rw [GB.colSpan_le_iff]
    intro q
    rw [Submodule.mem_map]
    refine ⟨∑ j ∈ B, w j q • GB.col x j, ?_, ?_⟩
    · apply Submodule.sum_mem
      intro j _
      exact Submodule.smul_mem _ _ (GB.col_mem_colSpan x j)
    · funext k
      rw [hU]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GB.col, GB.matExt]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
  calc GB.matRank (GB.matExt A B (GB.opVec T) w x)
      = GB.frk (GB.colSpan (GB.matExt A B (GB.opVec T) w x)) := rfl
    _ ≤ GB.frk ((GB.colSpan x).map U) := Submodule.finrank_mono hle
    _ ≤ GB.frk (GB.colSpan x) := Submodule.finrank_map_le U (GB.colSpan x)
    _ = GB.matRank x := rfl

end Work.LT

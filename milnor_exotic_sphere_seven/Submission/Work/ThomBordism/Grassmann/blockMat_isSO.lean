import Mathlib
import Submission.Work.ThomBordism.Grassmann.FibreBaseDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann

open Matrix

/-!
# `diag(B,1)` is orthogonal when `B` is

The block matrix `blockMat k B = diag(B,1)` (`B` acting on the first `k-1` coordinates, `1` on the
last one) is the matrix of the block embedding `O(k-1) → O(k)` that adds a fixed unit vector.  Here
we record the two facts about it needed downstream: it is a reindexed honest block matrix, and it
lies in `SO(k)` when `B` lies in `SO(k-1)`.
-/

/-- `blockMat k B` is `diag(B,1)` viewed through the splitting `Fin (k-1) ⊕ Fin 1 ≃ Fin k` of the
index set (the first `k-1` coordinates, then the last one). -/
theorem blockMat_eq_reindex (k : ℕ) (hk : 1 ≤ k) (B : Matrix (Fin (k-1)) (Fin (k-1)) ℝ) :
    blockMat k B =
      Matrix.reindex (sumEquiv k hk) (sumEquiv k hk)
        (Matrix.fromBlocks B (0 : Matrix (Fin (k-1)) (Fin 1) ℝ)
          (0 : Matrix (Fin 1) (Fin (k-1)) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  have hsymm_ct : ∀ a : Fin (k-1), (sumEquiv k hk).symm (ct k hk a) = Sum.inl a :=
    fun a => by simpa using Equiv.symm_apply_apply (sumEquiv k hk) (Sum.inl a)
  have hsymm_last : (sumEquiv k hk).symm (lastk k hk) = Sum.inr 0 := by
    simpa using Equiv.symm_apply_apply (sumEquiv k hk) (Sum.inr 0)
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases eq_lastk_or_eq_ct k hk i with rfl | ⟨a, rfl⟩ <;>
    rcases eq_lastk_or_eq_ct k hk j with rfl | ⟨b, rfl⟩ <;>
    simp [hsymm_ct, hsymm_last]

/-- **`diag(B,1) ∈ SO(k)` for `B ∈ SO(k-1)`.**  Adding a `1` in the last coordinate of an orthogonal
matrix with determinant `1` preserves both `Aᵀ A = 1` and `det A = 1`. -/
theorem blockMat_isSO (k : ℕ) (hk : 1 ≤ k) (B : Matrix (Fin (k-1)) (Fin (k-1)) ℝ)
    (hB : Work.ThomBordism.Grassmann.IsSO B) :
    Work.ThomBordism.Grassmann.IsSO (Work.ThomBordism.Grassmann.blockMat k B) := by
  constructor
  · -- orthogonality, entrywise: split each sum over `Fin k` into its first `k-1` terms and the last
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    rw [sum_fin_eq k hk (fun t => blockMat k B t i * blockMat k B t j)]
    rcases eq_lastk_or_eq_ct k hk i with rfl | ⟨a, rfl⟩
    · rcases eq_lastk_or_eq_ct k hk j with rfl | ⟨b, rfl⟩
      · simp
      · simp [(ct_ne_lastk k hk b).symm]
    · rcases eq_lastk_or_eq_ct k hk j with rfl | ⟨b, rfl⟩
      · simp [(ct_ne_lastk k hk a)]
      · simp only [blockMat_ct_ct, blockMat_last_ct, mul_zero]
        have h1 : (∑ x : Fin (k-1), B x a * B x b) =
            (1 : Matrix (Fin (k-1)) (Fin (k-1)) ℝ) a b := by
          have := congrFun (congrFun hB.1 a) b
          simpa [Matrix.mul_apply, Matrix.transpose_apply] using this
        rw [h1, add_zero]
        exact (congrFun (congrFun (Matrix.submatrix_one (ct k hk) (ct_injective k hk)) a) b).symm
  · -- determinant: `det (diag(B,1)) = det B * det 1 = 1`
    rw [blockMat_eq_reindex k hk B, Matrix.det_reindex]
    rw [show (sumEquiv k hk).trans (sumEquiv k hk).symm = 1 from Equiv.ext fun x => by simp]
    rw [Equiv.Perm.sign_one, Matrix.det_fromBlocks_zero₁₂, hB.2, Matrix.det_one, mul_one]
    simp

end Work.ThomBordism.Grassmann

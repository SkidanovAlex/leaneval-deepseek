import Mathlib

namespace Work.Mostow

theorem detFin2BlockDiag {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (B : ι → Matrix (Fin 2) (Fin 2) R) :
    (Matrix.of (fun (x y : ι × Fin 2) => if x.1 = y.1 then B x.1 x.2 y.2 else 0)).det = ∏ i, (B i).det := by
  -- Identify the matrix with the block diagonal of the `B i`, reindexed by `ι × Fin 2 ≃ Fin 2 × ι`.
  have hM : Matrix.of (fun (x y : ι × Fin 2) => if x.1 = y.1 then B x.1 x.2 y.2 else 0)
      = (Matrix.blockDiagonal B).submatrix (Equiv.prodComm ι (Fin 2)) (Equiv.prodComm ι (Fin 2)) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Matrix.blockDiagonal_apply']
  rw [hM, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]

end Work.Mostow

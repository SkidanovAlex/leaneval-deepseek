import Mathlib
import Submission.Work.KT.Psi.psi3sum_Setup

/-!
# `Work.KT.Psi.clsM_sumBlk_cubePartP`

The `K₀`-class of `(p ⊕ q)^{⊗3}` cut down by the spectral projector of the cyclic permutation of
the three tensor factors is the class of the unreindexed triple power `cubePartP λ (p ⊕ q)`.

Concretely, the index set of `p ⊕ q` is `Fin p.1 ⊕ Fin q.1`, whereas `Mat.sum` reindexes the block
matrix `fromBlocks p.2 0 0 q.2` to `Fin (p.1 + q.1)` along `finSumFinEquiv`.  The triple tensor
product `kron3g (sumBlk p q)` (on `SQ (Fin p.1 ⊕ Fin q.1)`) and the cyclic projector
`Cp (Fin p.1 ⊕ Fin q.1) λ` are therefore exactly the `finSumFinEquiv`-reindexing of
`cubePartP λ (p.sum q)` (on `SQ (Fin (p.1 + q.1))`), and `clsM` (equivalently `clsI`) is invariant
under reindexing (`clsI_reindex`).  No idempotency hypothesis is needed.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

theorem clsM_sumBlk_cubePartP {A : Type} [Ring A] [Algebra ℂ A] (p q : Work.KT.Mat A) (lam : ℂ) :
    Work.KT.Psi.clsM (Work.KT.Psi.SQ (Fin p.1 ⊕ Fin q.1))
      (Work.KT.Psi.kron3g (Work.KT.Psi.sumBlk p q) * Work.KT.Psi.Cp (Fin p.1 ⊕ Fin q.1) lam)
      = Work.KT.Psi.clsM (Work.KT.Psi.SQ (Fin (p.1 + q.1))) (Work.KT.cubePartP lam (p.sum q)) := by
  -- `cyc3 (Fin n)` and `cycPermP n` are the same cyclic permutation.
  have hcyc : cyc3 (Fin (p.1 + q.1)) = cycPermP (p.1 + q.1) := rfl
  set e := finSumFinEquiv (m := p.1) (n := q.1) with he
  -- The triple tensor product reindexes to the triple tensor product of `(p ⊕ q).2`.
  have hk : Matrix.reindex (e3 e) (e3 e) (kron3g (sumBlk p q)) = kron3g (p.sum q).2 := by
    simp only [kron3g, kron3m, e3]
    rw [← Matrix.kroneckerMap_reindex (fun x y : A => x * y)]
    rw [← Matrix.kroneckerMap_reindex (fun x y : A => x * y)]
    rfl
  -- The cyclic spectral projector reindexes to the one of `cycPermP (p.1 + q.1)`.
  have hp : Matrix.reindex (e3 e) (e3 e) (Cp (Fin p.1 ⊕ Fin q.1) lam) =
      algebraMap ℂ A (1 / 3) •
        (1 + algebraMap ℂ A lam⁻¹ • Equiv.Perm.permMatrix A (cycPermP (p.1 + q.1)) +
          algebraMap ℂ A ((lam⁻¹) ^ 2) •
            (Equiv.Perm.permMatrix A (cycPermP (p.1 + q.1)) *
              Equiv.Perm.permMatrix A (cycPermP (p.1 + q.1)))) := by
    simp only [Cp, reindex_add', reindex_one', reindex_smul, reindex_mul',
      reindex_permMatrix, e3_cyc3, hcyc]
  -- The product reindexes to `cubePartP lam (p.sum q)`.
  have hmain : Matrix.reindex (e3 e) (e3 e)
      (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam) = cubePartP lam (p.sum q) := by
    rw [reindex_mul', hk, hp]
    rfl
  rw [hmain.symm]
  exact (clsI_reindex (e3 e) (kron3g (sumBlk p q) * Cp (Fin p.1 ⊕ Fin q.1) lam)).symm

end

end Work.KT.Psi

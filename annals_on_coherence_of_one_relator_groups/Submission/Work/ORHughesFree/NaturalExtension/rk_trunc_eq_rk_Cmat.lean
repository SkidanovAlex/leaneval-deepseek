import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.RankAPI.rk_reindex

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

/-- The identification `Fin (n+1) ≃ Fin (1*(n+1))` which puts a `Fin (n+1)`-index into the
first (`Fin 1`) block of `Fin (1*(n+1)) ≃ Fin 1 × Fin (n+1)`; its inverse is `Fin.modNat`. -/
noncomputable def finOneProdEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (1 * (n + 1)) where
  toFun s := finProdFinEquiv ((0 : Fin 1), s)
  invFun i := i.modNat
  left_inv s := by
    show (finProdFinEquiv ((0 : Fin 1), s)).modNat = s
    exact Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd (0 : Fin 1) s
  right_inv i := by
    show finProdFinEquiv ((0 : Fin 1), i.modNat) = i
    have h : ((0 : Fin 1), i.modNat) = finProdFinEquiv.symm i := by
      rw [finProdFinEquiv_symm_apply]
      exact Prod.ext (Subsingleton.elim _ _) rfl
    rw [h, Equiv.apply_symm_apply]

/-- The `(n+1) × (n+1)` matrix `Cmat p n` reindexed by `finOneProdEquiv n` is the truncation
`trunc (n+1) (oneByOne p)`: both have `(i,j)`-entry `ofAdd i • coeffElt p (j - i)`, since
`trunc`'s block index is forced to `0` (a `Fin 1`). -/
theorem trunc_oneByOne_eq_reindex_Cmat {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R) (n : ℕ) :
    trunc (n + 1) (oneByOne p) =
      (Matrix.reindex (finOneProdEquiv n) (finOneProdEquiv n)) (Cmat p n) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, trunc_apply]
  show (Multiplicative.ofAdd ((i.modNat : ℕ) : ℤ)) •
      coeffElt (oneByOne p i.divNat j.divNat) (((j.modNat : ℕ) : ℤ) - ((i.modNat : ℕ) : ℤ))
    = Cmat p n (i.modNat) (j.modNat)
  rw [Cmat]
  simp [oneByOne]

/-- The truncation `trunc (n+1) (oneByOne p)` (of type `Matrix (Fin (1*(n+1))) (Fin (1*(n+1))) R`)
is `Cmat p n` up to the identification `Fin (1*(n+1)) ≃ Fin (n+1)`; use `trunc_apply'` in
`NaturalExtension/Defs.lean` (with `n = m = 1`, so `q.divNat`/`p.divNat` are forced to `0` and
`finProdFinEquiv_fst`/`finProdFinEquiv_snd` identify `q.modNat` with the flat index), and the
reindexing-invariance of `rk` (`Work.ORHughesFree.RankAPI.rk_reindex`). -/
theorem rk_trunc_eq_rk_Cmat {R : Type u} [Ring R] [VonNeumannRegularRing R]
    [MulSemiringAction (Multiplicative ℤ) R] (rk : SylvesterRank R) (p : SkewL R) (n : ℕ) :
    rk.rk (1 * (n + 1)) (1 * (n + 1)) (trunc (n + 1) (oneByOne p)) =
      rk.rk (n + 1) (n + 1) (Cmat p n) := by
  rw [trunc_oneByOne_eq_reindex_Cmat]
  exact RankAPI.rk_reindex rk (finOneProdEquiv n) (finOneProdEquiv n) (Cmat p n)

end Work.ORHughesFree.NaturalExtension

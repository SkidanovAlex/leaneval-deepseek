import Mathlib
import Submission.Work.KT.Basic

namespace Work.KT

open Matrix

noncomputable section

/-! ## The index-swap reindexing

`Fin (n * k) ≃ Fin (k * n)` induced by `(i, j) ↦ (j, i)`; this is the reindexing along which the
Kronecker product of square matrices becomes the Kronecker product with the factors exchanged. -/
def swapFinEquiv (n k : ℕ) : Fin (n * k) ≃ Fin (k * n) :=
  (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin n) (Fin k))).trans finProdFinEquiv

/-- On `finProdFinEquiv`-indices, `swapFinEquiv` is `Prod.swap`. -/
lemma swapFinEquiv_symm_finProdFinEquiv (n k : ℕ) (a : Fin k) (b : Fin n) :
    (swapFinEquiv n k).symm (finProdFinEquiv (a, b)) = finProdFinEquiv (b, a) := by
  simp [swapFinEquiv, Equiv.trans_apply, Equiv.prodComm_apply]

/-- On `finProdFinEquiv`-indices, the inverse of `swapFinEquiv` acts as `Prod.swap`. -/
lemma finProdFinEquiv_symm_swapFinEquiv (n k : ℕ) (a : Fin k) (b : Fin n) :
    finProdFinEquiv.symm ((swapFinEquiv n k).symm (finProdFinEquiv (a, b))) = (b, a) := by
  rw [swapFinEquiv_symm_finProdFinEquiv]
  simp

/-- The inverse of `swapFinEquiv` sends `finProdFinEquiv x` to `finProdFinEquiv x.swap`. -/
lemma finProdFinEquiv_symm_swapFinEquiv' (n k : ℕ) (i : Fin (k * n)) :
    finProdFinEquiv.symm ((swapFinEquiv n k).symm i)
      = ((finProdFinEquiv.symm i).2, (finProdFinEquiv.symm i).1) := by
  simp [swapFinEquiv, Equiv.trans_apply, Equiv.prodComm_apply]

/-- The `(· * ·)`-Kronecker product with the factors exchanged is the reindexing of the original
Kronecker product along `swapFinEquiv` (over a commutative ring). -/
lemma kronMat_swap {A : Type} [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    (n k : ℕ) (P : Matrix (Fin n) (Fin n) A) (Q : Matrix (Fin k) (Fin k) A) :
    Matrix.reindex (swapFinEquiv n k) (swapFinEquiv n k) (kronMatR P Q) = kronMatR Q P := by
  ext i j
  simp only [kronMatR, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  rw [finProdFinEquiv_symm_swapFinEquiv' n k i, finProdFinEquiv_symm_swapFinEquiv' n k j]
  exact hcomm _ _

/-! ## `Mat.MvN` versus the Kronecker product -/

/-- `Mat.MvN` is respected by the Kronecker product in its first variable, the second factor being
idempotent (over a commutative ring). -/
lemma mvN_kron_left {A : Type} [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    {p q p' : Mat A} (hp : Mat.MvN p p') (hq : q.IsIdem) :
    Mat.MvN (p.kron q) (p'.kron q) := by
  obtain ⟨a, b, hba, hab⟩ := hp
  refine ⟨kronMatR a q.2, kronMatR b q.2, ?_, ?_⟩
  · change kronMatR b q.2 * kronMatR a q.2 = kronMatR p.2 q.2
    rw [← kronMatR_mul hcomm b a q.2 q.2, hba, hq]
  · change kronMatR a q.2 * kronMatR b q.2 = kronMatR p'.2 q.2
    rw [← kronMatR_mul hcomm a b q.2 q.2, hab, hq]

/-- `Mat.MvN` is respected by the Kronecker product in its second variable, the first factor being
idempotent (over a commutative ring). -/
lemma mvN_kron_right {A : Type} [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    {p q q' : Mat A} (hq : Mat.MvN q q') (hp : p.IsIdem) :
    Mat.MvN (p.kron q) (p.kron q') := by
  obtain ⟨a, b, hba, hab⟩ := hq
  refine ⟨kronMatR p.2 a, kronMatR p.2 b, ?_, ?_⟩
  · change kronMatR p.2 b * kronMatR p.2 a = kronMatR p.2 q.2
    rw [← kronMatR_mul hcomm p.2 p.2 b a, hp, hba]
  · change kronMatR p.2 a * kronMatR p.2 b = kronMatR p.2 q'.2
    rw [← kronMatR_mul hcomm p.2 p.2 a b, hp, hab]

/-- The Kronecker product of square matrices is commutative up to reindexing, hence up to
Murray–von Neumann equivalence (over a commutative ring). -/
lemma mvN_kron_comm {A : Type} [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p q : Mat A) :
    Mat.MvN (p.kron q) (q.kron p) := by
  have hk : (q.kron p).2
      = Matrix.reindex (swapFinEquiv p.1 q.1) (swapFinEquiv p.1 q.1) (p.kron q).2 := by
    rw [Mat.kron_snd, Mat.kron_snd]
    exact (kronMat_swap hcomm p.1 q.1 p.2 q.2).symm
  have hmat : q.kron p
      = ⟨q.1 * p.1,
          Matrix.reindex (swapFinEquiv p.1 q.1) (swapFinEquiv p.1 q.1) (p.kron q).2⟩ := by
    rw [← hk]
    rfl
  rw [hmat]
  exact Mat.mvN_reindex (swapFinEquiv p.1 q.1) (p.kron q).2

/-- Over a commutative ring: `Mat.MvN` is respected by the Kronecker product (in each variable,
with the other factor idempotent), and the Kronecker product is commutative up to Murray–von
Neumann equivalence. -/
theorem mvN_comm :
    (∀ (A : Type) [Ring A], (∀ x y : A, x * y = y * x) → ∀ (p q p' : Mat A),
      Mat.MvN p p' → q.IsIdem → Mat.MvN (p.kron q) (p'.kron q)) ∧
    (∀ (A : Type) [Ring A], (∀ x y : A, x * y = y * x) → ∀ (p q q' : Mat A),
      Mat.MvN q q' → p.IsIdem → Mat.MvN (p.kron q) (p.kron q')) ∧
    (∀ (A : Type) [Ring A], (∀ x y : A, x * y = y * x) → ∀ (p q : Mat A),
      Mat.MvN (p.kron q) (q.kron p)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A _ hcomm p q p' hp hq
    exact mvN_kron_left hcomm hp hq
  · intro A _ hcomm p q q' hq hp
    exact mvN_kron_right hcomm hq hp
  · intro A _ hcomm p q
    exact mvN_kron_comm hcomm p q

end

end Work.KT

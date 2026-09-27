import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic

/-!
# `Work.KT.sum_mvN_assoc` — associativity of the block sum up to Murray–von Neumann equivalence

The block sum `p ⊕ q` of `Submission/Work/KT/Defs.lean` is *not* literally associative on the nose:
`(p ⊕ q) ⊕ r` and `p ⊕ (q ⊕ r)` are square matrices of the *different* sizes
`(p.1 + q.1) + r.1` and `p.1 + (q.1 + r.1)`.  They are, however, related by the reindexing
`Fin ((n+m)+k) ≃ Fin (n+(m+k))` that reassociates the index triples, and reindexing is an
isomorphism of matrix rings, hence a Murray–von Neumann equivalence (`Mat.mvN_reindex`).

We first transport the associator of `⊕` (`Equiv.sumAssoc`) along `finSumFinEquiv` to an
equivalence `sumMvN_assocEquiv n m k` of the two `Fin`-types, then prove that reindexing the
matrix of `(p ⊕ q) ⊕ r` along it gives the matrix of `p ⊕ (q ⊕ r)`.  The proof is a chain of
elementary reindexing identities for `Matrix.fromBlocks`:

* `sumMvN_reindex_fromBlocks_sumCongr` — reindexing a block matrix by `sumCongr`;
* `sumMvN_reindex_fromBlocks_sumAssoc` — reindexing a doubly blocked matrix by `sumAssoc`.

No commutativity of the coefficient ring is used, and no idempotency of `p, q, r` is needed:
`Mat.MvN` here is the equivalence relation "there exist intertwining rectangular matrices", which
holds for a matrix and any reindexing of it.
-/

namespace Work.KT

open Matrix

/-- The index equivalence `Fin ((n+m)+k) ≃ Fin (n+(m+k))` reassociating a triple of indices:
it commutes with the canonical identifications `Fin a ⊕ Fin b ≃ Fin (a+b)`, i.e. it is the
transport of `Equiv.sumAssoc` along `finSumFinEquiv`. -/
def sumMvN_assocEquiv (n m k : ℕ) : Fin ((n + m) + k) ≃ Fin (n + (m + k)) :=
  (finSumFinEquiv.symm : Fin ((n+m)+k) ≃ Fin (n+m) ⊕ Fin k).trans
    ((Equiv.sumCongr (finSumFinEquiv.symm : Fin (n+m) ≃ Fin n ⊕ Fin m) (Equiv.refl (Fin k))).trans
      ((Equiv.sumAssoc (Fin n) (Fin m) (Fin k)).trans
        ((Equiv.sumCongr (Equiv.refl (Fin n)) (finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k))).trans
          (finSumFinEquiv : Fin n ⊕ Fin (m+k) ≃ Fin (n+(m+k))))))

/-- Composing `sumMvN_assocEquiv` on the left with `finSumFinEquiv` (from `Fin (n+m) ⊕ Fin k`)
unfolds to the plain associator of `⊕` transported to `Fin`. -/
lemma sumMvN_assocEquiv_comp (n m k : ℕ) :
    (finSumFinEquiv).trans (sumMvN_assocEquiv n m k) =
      (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin k))).trans
        ((Equiv.sumAssoc (Fin n) (Fin m) (Fin k)).trans
          ((Equiv.sumCongr (Equiv.refl (Fin n)) finSumFinEquiv).trans finSumFinEquiv)) := by
  unfold sumMvN_assocEquiv
  rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

/-! ## Reindexing lemmas -/

/-- Reindexing twice is reindexing by the composite. -/
lemma sumMvN_reindex_comp {α : Type} {m n m' n' m'' n'' : Type}
    (e : m ≃ m') (f : n ≃ n') (e' : m' ≃ m'') (f' : n' ≃ n'') (X : Matrix m n α) :
    Matrix.reindex e' f' (Matrix.reindex e f X) = Matrix.reindex (e.trans e') (f.trans f') X := by
  have h := Matrix.reindex_trans (α := α) e f e' f'
  exact congrArg (fun g : Matrix m n α ≃ Matrix m'' n'' α => g X) h

/-- Reindexing a block diagonal matrix by a `sumCongr` acts on the two blocks separately. -/
lemma sumMvN_reindex_fromBlocks_sumCongr {α : Type} [Zero α] {ι₁ ι₂ κ₁ κ₂ : Type}
    (e₁ : ι₁ ≃ κ₁) (e₂ : ι₂ ≃ κ₂)
    (A : Matrix ι₁ ι₁ α) (B : Matrix ι₂ ι₂ α) :
    Matrix.reindex (Equiv.sumCongr e₁ e₂) (Equiv.sumCongr e₁ e₂) (Matrix.fromBlocks A 0 0 B)
      = Matrix.fromBlocks (Matrix.reindex e₁ e₁ A) 0 0 (Matrix.reindex e₂ e₂ B) := by
  ext x y
  rcases x with a | b <;> rcases y with c | d <;>
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Reindexing the doubly blocked matrix `(A ⊕ B) ⊕ C` by the associator of `⊕` gives
`A ⊕ (B ⊕ C)`. -/
lemma sumMvN_reindex_fromBlocks_sumAssoc {α : Type} [Zero α] {ι κ ν : Type}
    (A : Matrix ι ι α) (B : Matrix κ κ α) (C : Matrix ν ν α) :
    Matrix.reindex (Equiv.sumAssoc ι κ ν) (Equiv.sumAssoc ι κ ν)
      (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B) 0 0 C)
      = Matrix.fromBlocks A 0 0 (Matrix.fromBlocks B 0 0 C) := by
  ext x y
  rcases x with a | (b | c) <;> rcases y with a' | (b' | c') <;>
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Reindexing by the identity equivalence is the identity. -/
lemma sumMvN_reindex_refl {α : Type} {m n : Type} (X : Matrix m n α) :
    Matrix.reindex (Equiv.refl m) (Equiv.refl n) X = X := by
  ext i j; simp [Matrix.reindex_apply]

/-- Reindexing by `e` and then by `e.symm` is the identity. -/
lemma sumMvN_reindex_symm_comp {α : Type} {m n : Type} (e : m ≃ n) (X : Matrix m m α) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e X) = X := by
  rw [sumMvN_reindex_comp e e e.symm e.symm X, Equiv.self_trans_symm]
  exact sumMvN_reindex_refl X

/-! ## The key matrix identity -/

/-- **The heart of the associativity statement**: after reindexing the indices by
`sumMvN_assocEquiv`, the matrix of `(p ⊕ q) ⊕ r` *is* the matrix of `p ⊕ (q ⊕ r)`. -/
lemma sumMvN_reindex_sum_assoc {R : Type} [Ring R] (n m k : ℕ)
    (P : Matrix (Fin n) (Fin n) R) (Q : Matrix (Fin m) (Fin m) R) (R' : Matrix (Fin k) (Fin k) R) :
    Matrix.reindex (sumMvN_assocEquiv n m k) (sumMvN_assocEquiv n m k)
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks
          (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P 0 0 Q)) 0 0 R'))
    = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks P 0 0
          (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Q 0 0 R'))) := by
  rw [sumMvN_reindex_comp]
  rw [sumMvN_assocEquiv_comp]
  rw [← sumMvN_reindex_comp]
  rw [sumMvN_reindex_fromBlocks_sumCongr]
  rw [sumMvN_reindex_symm_comp, sumMvN_reindex_refl]
  rw [← sumMvN_reindex_comp]
  rw [sumMvN_reindex_fromBlocks_sumAssoc]
  rw [← sumMvN_reindex_comp]
  rw [sumMvN_reindex_fromBlocks_sumCongr]
  rw [sumMvN_reindex_refl]

theorem sum_mvN_assoc :
    ∀ (R : Type) [Ring R] (p q r : Mat R),
      Mat.MvN ((p.sum q).sum r) (p.sum (q.sum r)) := by
  intro R _ p q r
  obtain ⟨n, P⟩ := p
  obtain ⟨m, Q⟩ := q
  obtain ⟨k, R'⟩ := r
  have h := Mat.mvN_reindex (sumMvN_assocEquiv n m k)
    (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks
        (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P 0 0 Q)) 0 0 R'))
  rw [sumMvN_reindex_sum_assoc n m k P Q R'] at h
  exact h

end Work.KT

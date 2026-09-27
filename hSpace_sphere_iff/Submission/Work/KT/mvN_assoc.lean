import Mathlib
import Submission.Work.KT.Basic

/-!
# `Work.KT.mvN_assoc` — associativity and unit of the Kronecker product up to MvN equivalence

The Kronecker product `Mat.kron` of `Submission/Work/KT/Defs.lean` models the tensor product of
"bundles": `(p ⊗ q) ⊗ r` and `p ⊗ (q ⊗ r)` are matrices of *different* sizes, related by the
reindexing `Fin ((n*m)*k) ≃ Fin (n*(m*k))` that reassociates index triples.  Reindexing is an
isomorphism of matrix rings, hence a Murray–von Neumann equivalence (`Mat.mvN_reindex`), and the
entries of the two products agree by associativity of the multiplication of `A` (via
`Matrix.kronecker_assoc`).  No commutativity is used, and no idempotency of `p, q, r` is needed:
`Mat.MvN` is an equivalence relation on matrices *of the same size* (not the usual one on
idempotents), and the witnesses here are the reindexing matrices, which are invertible.

The unit statement `1₁ ⊗ p ~ p` is the same computation with the index equivalence
`Fin 1 × Fin n ≃ Fin n`.
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## Re-associating the index types -/

/-- The index equivalence `(Fin n × Fin m) × Fin k ≃ Fin n × (Fin m × Fin k)`, transported to
`Fin ((n*m)*k) ≃ Fin (n*(m*k))` along `finProdFinEquiv`. -/
def mvNassoc_assocEquiv (n m k : ℕ) : Fin ((n*m)*k) ≃ Fin (n*(m*k)) :=
  ((finProdFinEquiv.symm : Fin ((n*m)*k) ≃ Fin (n*m) × Fin k).trans
    ((Equiv.prodCongr (finProdFinEquiv.symm : Fin (n*m) ≃ Fin n × Fin m)
      (Equiv.refl (Fin k))) :
      Fin (n*m) × Fin k ≃ (Fin n × Fin m) × Fin k)).trans
    ((((Equiv.prodAssoc (Fin n) (Fin m) (Fin k)) :
      (Fin n × Fin m) × Fin k ≃ Fin n × (Fin m × Fin k)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin n)) (finProdFinEquiv)) :
        Fin n × (Fin m × Fin k) ≃ Fin n × Fin (m*k))).trans
      (finProdFinEquiv : Fin n × Fin (m*k) ≃ Fin (n*(m*k))))

/-- How `mvNassoc_assocEquiv` acts on a triple of indices. -/
lemma mvNassoc_assocEquiv_apply (n m k : ℕ) (i : Fin n) (j : Fin m) (l : Fin k) :
    mvNassoc_assocEquiv n m k (finProdFinEquiv (finProdFinEquiv (i, j), l)) =
      finProdFinEquiv (i, finProdFinEquiv (j, l)) := by
  simp only [mvNassoc_assocEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply,
    Equiv.prodAssoc_apply, Equiv.symm_apply_apply, Prod.map_apply]

/-- The two ways of reading `((i,j),k)` as a single index of `Fin (n*(m*k))` agree. -/
lemma mvNassoc_assocEquiv_comp (n m k : ℕ) :
    (Equiv.prodCongr (finProdFinEquiv : Fin n × Fin m ≃ Fin (n*m)) (Equiv.refl (Fin k))).trans
        ((finProdFinEquiv : Fin (n*m) × Fin k ≃ Fin ((n*m)*k)).trans
          (mvNassoc_assocEquiv n m k))
      = (Equiv.prodAssoc (Fin n) (Fin m) (Fin k)).trans
        ((Equiv.prodCongr (Equiv.refl (Fin n))
            (finProdFinEquiv : Fin m × Fin k ≃ Fin (m*k))).trans
          (finProdFinEquiv : Fin n × Fin (m*k) ≃ Fin (n*(m*k)))) := by
  ext x
  obtain ⟨⟨i, j⟩, l⟩ := x
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply, Equiv.prodAssoc_apply,
    mvNassoc_assocEquiv_apply, Prod.map_apply]

/-! ## Reindexing vs. the Kronecker product -/

/-- Reindexing twice is reindexing by the composite. -/
lemma mvNassoc_reindex_reindex {α : Type*} {m n m' n' m'' n'' : Type*}
    (e : m ≃ m') (f : n ≃ n') (e' : m' ≃ m'') (f' : n' ≃ n'') (X : Matrix m n α) :
    Matrix.reindex e' f' (Matrix.reindex e f X) = Matrix.reindex (e.trans e') (f.trans f') X := by
  have h := Matrix.reindex_trans (α := α) e f e' f'
  exact congrArg (fun g : Matrix m n α ≃ Matrix m'' n'' α => g X) h

/-- Reindexing the left factor of a Kronecker product. -/
lemma mvNassoc_kron_reindex_left {A : Type} [Mul A] {ι κ ν : Type}
    (X : Matrix ι ι A) (Y : Matrix ν ν A) (e : ι ≃ κ) :
    Matrix.kroneckerMap (· * ·) (Matrix.reindex e e X) Y =
      Matrix.reindex (Equiv.prodCongr e (Equiv.refl ν)) (Equiv.prodCongr e (Equiv.refl ν))
        (Matrix.kroneckerMap (· * ·) X Y) := by
  rw [Matrix.reindex_apply e e X,
    Matrix.reindex_apply (Equiv.prodCongr e (Equiv.refl ν)) (Equiv.prodCongr e (Equiv.refl ν))
      (Matrix.kroneckerMap (· * ·) X Y),
    Matrix.kroneckerMap_submatrix_left]
  rfl

/-- Reindexing the right factor of a Kronecker product. -/
lemma mvNassoc_kron_reindex_right {A : Type} [Mul A] {ι κ ν : Type}
    (X : Matrix ι ι A) (Y : Matrix ν ν A) (e : ν ≃ κ) :
    Matrix.kroneckerMap (· * ·) X (Matrix.reindex e e Y) =
      Matrix.reindex (Equiv.prodCongr (Equiv.refl ι) e) (Equiv.prodCongr (Equiv.refl ι) e)
        (Matrix.kroneckerMap (· * ·) X Y) := by
  rw [Matrix.reindex_apply e e Y,
    Matrix.reindex_apply (Equiv.prodCongr (Equiv.refl ι) e) (Equiv.prodCongr (Equiv.refl ι) e)
      (Matrix.kroneckerMap (· * ·) X Y),
    Matrix.kroneckerMap_submatrix_right]
  rfl

/-- **The heart of the associativity statement**: after reindexing the indices by
`mvNassoc_assocEquiv`, the matrix `(p ⊗ q) ⊗ r` *is* the matrix `p ⊗ (q ⊗ r)`. -/
lemma mvNassoc_reindex_kronMatR_assoc {A : Type} [Ring A] {n m k : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (N : Matrix (Fin m) (Fin m) A) (P : Matrix (Fin k) (Fin k) A) :
    Matrix.reindex (mvNassoc_assocEquiv n m k) (mvNassoc_assocEquiv n m k)
        (kronMatR (kronMatR M N) P)
      = kronMatR M (kronMatR N P) := by
  simp only [kronMatR]
  rw [mvNassoc_kron_reindex_left (Matrix.kroneckerMap (· * ·) M N) P finProdFinEquiv]
  rw [mvNassoc_reindex_reindex finProdFinEquiv finProdFinEquiv
    (mvNassoc_assocEquiv n m k) (mvNassoc_assocEquiv n m k)]
  rw [mvNassoc_reindex_reindex (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin k)))
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin k)))
    (finProdFinEquiv.trans (mvNassoc_assocEquiv n m k))
    (finProdFinEquiv.trans (mvNassoc_assocEquiv n m k))]
  rw [mvNassoc_kron_reindex_right M (Matrix.kroneckerMap (· * ·) N P) finProdFinEquiv]
  rw [mvNassoc_reindex_reindex (Equiv.prodCongr (Equiv.refl (Fin n)) finProdFinEquiv)
    (Equiv.prodCongr (Equiv.refl (Fin n)) finProdFinEquiv) finProdFinEquiv finProdFinEquiv]
  rw [← Matrix.kronecker_assoc M N P]
  rw [mvNassoc_reindex_reindex (Equiv.prodAssoc (Fin n) (Fin m) (Fin k))
    (Equiv.prodAssoc (Fin n) (Fin m) (Fin k))
    ((Equiv.prodCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finProdFinEquiv)
    ((Equiv.prodCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finProdFinEquiv)]
  rw [mvNassoc_assocEquiv_comp]

/-! ## The unit `1₁ ⊗ p` -/

/-- The index equivalence `Fin 1 × Fin n ≃ Fin n`. -/
def mvNassoc_oneProdEquiv (n : ℕ) : Fin 1 × Fin n ≃ Fin n where
  toFun := Prod.snd
  invFun := fun i => (0, i)
  left_inv := by
    intro p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv := by
    intro i
    rfl

/-- The Kronecker product with the `1 × 1` identity matrix is the original matrix, up to
reindexing. -/
lemma mvNassoc_kron_one_eq {A : Type} [Ring A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) :
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 1) (Fin 1) A) M
      = Matrix.reindex (mvNassoc_oneProdEquiv n).symm (mvNassoc_oneProdEquiv n).symm M := by
  ext i j
  have h : i.1 = j.1 := Subsingleton.elim _ _
  simp [Matrix.kroneckerMap_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.one_apply, mvNassoc_oneProdEquiv, h]

/-- `kronMatR 1 M` is a reindexing of `M`. -/
lemma mvNassoc_kronMatR_one_eq {A : Type} [Ring A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) :
    kronMatR (1 : Matrix (Fin 1) (Fin 1) A) M
      = Matrix.reindex ((mvNassoc_oneProdEquiv n).symm.trans finProdFinEquiv)
          ((mvNassoc_oneProdEquiv n).symm.trans finProdFinEquiv) M := by
  simp only [kronMatR]
  rw [mvNassoc_kron_one_eq]
  rw [mvNassoc_reindex_reindex (mvNassoc_oneProdEquiv n).symm (mvNassoc_oneProdEquiv n).symm
    finProdFinEquiv finProdFinEquiv]

/-! ## The two Murray–von Neumann statements -/

/-- Associativity of the Kronecker product up to `Mat.MvN`. -/
lemma mvNassoc_kron_assoc {A : Type} [Ring A] (p q r : Mat A) :
    Mat.MvN ((p.kron q).kron r) (p.kron (q.kron r)) := by
  have h := Mat.mvN_reindex (mvNassoc_assocEquiv p.1 q.1 r.1)
    (kronMatR (kronMatR p.2 q.2) r.2)
  rw [mvNassoc_reindex_kronMatR_assoc] at h
  exact h

/-- The unit law `1₁ ⊗ p ~ p`. -/
lemma mvNassoc_kron_unit {A : Type} [Ring A] (p : Mat A) :
    Mat.MvN ((Mat.one A 1).kron p) p := by
  refine Mat.mvN_symm ?_
  change Mat.MvN p (⟨1 * p.1, kronMatR (1 : Matrix (Fin 1) (Fin 1) A) p.2⟩ : Mat A)
  rw [mvNassoc_kronMatR_one_eq p.2]
  exact Mat.mvN_reindex ((mvNassoc_oneProdEquiv p.1).symm.trans finProdFinEquiv) p.2

/-- Associativity of the Kronecker product up to Murray–von Neumann equivalence, and the unit
`1₁ ⊗ p ~ p`.  No commutativity is needed. -/
theorem mvN_assoc :
    (∀ (A : Type) [Ring A] (p q r : Mat A),
      Mat.MvN ((p.kron q).kron r) (p.kron (q.kron r))) ∧
    (∀ (A : Type) [Ring A] (p : Mat A),
      Mat.MvN ((Mat.one A 1).kron p) p) := by
  exact ⟨fun A _ p q r => mvNassoc_kron_assoc p q r, fun A _ p => mvNassoc_kron_unit p⟩

end

end Work.KT

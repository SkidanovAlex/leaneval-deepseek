import Mathlib
import Submission.Work.KT.Basic

namespace Work.KT

open Matrix

/-!
# Additivity of the Kronecker product up to Murray–von Neumann equivalence

`p ⊗ (q ⊕ r) ~ (p ⊗ q) ⊕ (p ⊗ r)` and `(p ⊕ q) ⊗ r ~ (p ⊗ r) ⊕ (q ⊗ r)`.

Both statements are instances of a single matrix identity: the Kronecker product of `p` with a
block sum of `q` and `r` is, after the obvious reshuffling of the index set, the block sum of
`p ⊗ q` and `p ⊗ r`.  Since a matrix and its reindexing along a bijection of `Fin` types are
Murray–von Neumann equivalent (`Mat.mvN_reindex`), the results follow.

No commutativity of the coefficient ring is needed: `Mat.kron` uses the entrywise product only.
-/

/-! ## The reshuffling equivalences -/

/-- `α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)`, by the canonical pattern match. -/
def prodSumEquiv (α β γ : Type) : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ) where
  toFun x := match x.2 with
    | Sum.inl b => Sum.inl (x.1, b)
    | Sum.inr c => Sum.inr (x.1, c)
  invFun y := match y with
    | Sum.inl p => (p.1, Sum.inl p.2)
    | Sum.inr p => (p.1, Sum.inr p.2)
  left_inv := by rintro ⟨a, b | c⟩ <;> rfl
  right_inv := by rintro (⟨a, b⟩ | ⟨a, c⟩) <;> rfl

/-- `(α ⊕ β) × γ ≃ (α × γ) ⊕ (β × γ)`, by the canonical pattern match. -/
def sumProdEquiv (α β γ : Type) : (α ⊕ β) × γ ≃ (α × γ) ⊕ (β × γ) where
  toFun x := match x.1 with
    | Sum.inl a => Sum.inl (a, x.2)
    | Sum.inr b => Sum.inr (b, x.2)
  invFun y := match y with
    | Sum.inl p => (Sum.inl p.1, p.2)
    | Sum.inr p => (Sum.inr p.1, p.2)
  left_inv := by rintro ⟨a | b, c⟩ <;> rfl
  right_inv := by rintro (⟨a, c⟩ | ⟨b, c⟩) <;> rfl

/-- The reshuffling `Fin (n*(m+k)) ≃ Fin (n*m + n*k)` matching `p ⊗ (q ⊕ r)` with
`(p ⊗ q) ⊕ (p ⊗ r)`. -/
def reshuffleL (n m k : ℕ) : Fin (n * (m + k)) ≃ Fin (n * m + n * k) :=
  ((finProdFinEquiv : Fin n × Fin (m + k) ≃ Fin (n * (m + k))).symm).trans
   ((Equiv.prodCongr (Equiv.refl (Fin n))
      (finSumFinEquiv.symm : Fin (m + k) ≃ Fin m ⊕ Fin k)).trans
    ((prodSumEquiv (Fin n) (Fin m) (Fin k)).trans
     ((Equiv.sumCongr (finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m))
        (finProdFinEquiv : Fin n × Fin k ≃ Fin (n * k))).trans finSumFinEquiv)))

/-- The reshuffling `Fin ((n+m)*k) ≃ Fin (n*k + m*k)` matching `(p ⊕ q) ⊗ r` with
`(p ⊗ r) ⊕ (q ⊗ r)`. -/
def reshuffleR (n m k : ℕ) : Fin ((n + m) * k) ≃ Fin (n * k + m * k) :=
  ((finProdFinEquiv : Fin (n + m) × Fin k ≃ Fin ((n + m) * k)).symm).trans
   ((Equiv.prodCongr (finSumFinEquiv.symm : Fin (n + m) ≃ Fin n ⊕ Fin m)
      (Equiv.refl (Fin k))).trans
    ((sumProdEquiv (Fin n) (Fin m) (Fin k)).trans
     ((Equiv.sumCongr (finProdFinEquiv : Fin n × Fin k ≃ Fin (n * k))
        (finProdFinEquiv : Fin m × Fin k ≃ Fin (m * k))).trans finSumFinEquiv)))

/-! ## Values of the reshufflings and of their inverses on canonical indices -/

lemma reshuffleL_apply_inl (n m k : ℕ) (i : Fin n) (c : Fin m) :
    reshuffleL n m k (finProdFinEquiv (i, finSumFinEquiv (Sum.inl c))) =
      finSumFinEquiv (Sum.inl (finProdFinEquiv (i, c))) := by
  simp only [reshuffleL, prodSumEquiv, Equiv.coe_fn_mk, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.sumCongr_apply, Equiv.symm_apply_apply, Equiv.refl_apply,
    Prod.map_apply, Sum.map_inl]

lemma reshuffleL_apply_inr (n m k : ℕ) (i : Fin n) (c : Fin k) :
    reshuffleL n m k (finProdFinEquiv (i, finSumFinEquiv (Sum.inr c))) =
      finSumFinEquiv (Sum.inr (finProdFinEquiv (i, c))) := by
  simp only [reshuffleL, prodSumEquiv, Equiv.coe_fn_mk, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.sumCongr_apply, Equiv.symm_apply_apply, Equiv.refl_apply,
    Prod.map_apply, Sum.map_inr]

lemma reshuffleL_symm_inl (n m k : ℕ) (i : Fin n) (c : Fin m) :
    (reshuffleL n m k).symm (finSumFinEquiv (Sum.inl (finProdFinEquiv (i, c)))) =
      finProdFinEquiv (i, finSumFinEquiv (Sum.inl c)) := by
  rw [Equiv.symm_apply_eq]
  exact (reshuffleL_apply_inl n m k i c).symm

lemma reshuffleL_symm_inr (n m k : ℕ) (i : Fin n) (c : Fin k) :
    (reshuffleL n m k).symm (finSumFinEquiv (Sum.inr (finProdFinEquiv (i, c)))) =
      finProdFinEquiv (i, finSumFinEquiv (Sum.inr c)) := by
  rw [Equiv.symm_apply_eq]
  exact (reshuffleL_apply_inr n m k i c).symm

lemma reshuffleR_apply_inl (n m k : ℕ) (i : Fin n) (a : Fin k) :
    reshuffleR n m k (finProdFinEquiv (finSumFinEquiv (Sum.inl i), a)) =
      finSumFinEquiv (Sum.inl (finProdFinEquiv (i, a))) := by
  simp only [reshuffleR, sumProdEquiv, Equiv.coe_fn_mk, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.sumCongr_apply, Equiv.symm_apply_apply, Equiv.refl_apply,
    Prod.map_apply, Sum.map_inl]

lemma reshuffleR_apply_inr (n m k : ℕ) (i : Fin m) (a : Fin k) :
    reshuffleR n m k (finProdFinEquiv (finSumFinEquiv (Sum.inr i), a)) =
      finSumFinEquiv (Sum.inr (finProdFinEquiv (i, a))) := by
  simp only [reshuffleR, sumProdEquiv, Equiv.coe_fn_mk, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.sumCongr_apply, Equiv.symm_apply_apply, Equiv.refl_apply,
    Prod.map_apply, Sum.map_inr]

lemma reshuffleR_symm_inl (n m k : ℕ) (i : Fin n) (a : Fin k) :
    (reshuffleR n m k).symm (finSumFinEquiv (Sum.inl (finProdFinEquiv (i, a)))) =
      finProdFinEquiv (finSumFinEquiv (Sum.inl i), a) := by
  rw [Equiv.symm_apply_eq]
  exact (reshuffleR_apply_inl n m k i a).symm

lemma reshuffleR_symm_inr (n m k : ℕ) (i : Fin m) (a : Fin k) :
    (reshuffleR n m k).symm (finSumFinEquiv (Sum.inr (finProdFinEquiv (i, a)))) =
      finProdFinEquiv (finSumFinEquiv (Sum.inr i), a) := by
  rw [Equiv.symm_apply_eq]
  exact (reshuffleR_apply_inr n m k i a).symm

/-! ## The two matrix identities -/

/-- `kronMat` is the rectangular Kronecker product of `Basic`. -/
lemma kronMat_eq_kronMatR {A : Type} [Ring A] {n m : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (N : Matrix (Fin m) (Fin m) A) :
    kronMat M N = kronMatR M N := rfl

/-- Reindexing `p ⊗ (q ⊕ r)` along `reshuffleL` gives `(p ⊗ q) ⊕ (p ⊗ r)`. -/
lemma reindex_kron_sum_eq {A : Type} [Ring A] (n m k : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (Q : Matrix (Fin m) (Fin m) A) (R : Matrix (Fin k) (Fin k) A) :
    Matrix.reindex (reshuffleL n m k) (reshuffleL n m k)
      (kronMat P (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Q 0 0 R))) =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (kronMat P Q) 0 0 (kronMat P R)) := by
  ext u v
  obtain ⟨y, rfl⟩ := Equiv.surjective finSumFinEquiv u
  obtain ⟨z, rfl⟩ := Equiv.surjective finSumFinEquiv v
  rcases y with a | a <;> rcases z with b | b <;>
  ( obtain ⟨⟨i, c⟩, rfl⟩ := Equiv.surjective finProdFinEquiv a
    obtain ⟨⟨j, d⟩, rfl⟩ := Equiv.surjective finProdFinEquiv b
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [reshuffleL_symm_inl, reshuffleL_symm_inr, kronMat_eq_kronMatR, kronMatR_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero] )

/-- Reindexing `(p ⊕ q) ⊗ r` along `reshuffleR` gives `(p ⊗ r) ⊕ (q ⊗ r)`. -/
lemma reindex_sum_kron_eq {A : Type} [Ring A] (n m k : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (Q : Matrix (Fin m) (Fin m) A) (R : Matrix (Fin k) (Fin k) A) :
    Matrix.reindex (reshuffleR n m k) (reshuffleR n m k)
      (kronMat (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P 0 0 Q)) R) =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (kronMat P R) 0 0 (kronMat Q R)) := by
  ext u v
  obtain ⟨y, rfl⟩ := Equiv.surjective finSumFinEquiv u
  obtain ⟨z, rfl⟩ := Equiv.surjective finSumFinEquiv v
  rcases y with a | a <;> rcases z with b | b <;>
  ( obtain ⟨⟨i, c⟩, rfl⟩ := Equiv.surjective finProdFinEquiv a
    obtain ⟨⟨j, d⟩, rfl⟩ := Equiv.surjective finProdFinEquiv b
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [reshuffleR_symm_inl, reshuffleR_symm_inr, kronMat_eq_kronMatR, kronMatR_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul] )

/-! ## Additivity -/

lemma mvN_kron_sum {A : Type} [Ring A] (n m k : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (Q : Matrix (Fin m) (Fin m) A) (R : Matrix (Fin k) (Fin k) A) :
    Mat.MvN (Mat.kron (⟨n, P⟩ : Mat A) (Mat.sum (⟨m, Q⟩ : Mat A) (⟨k, R⟩ : Mat A)))
      (Mat.sum (Mat.kron (⟨n, P⟩ : Mat A) (⟨m, Q⟩ : Mat A))
        (Mat.kron (⟨n, P⟩ : Mat A) (⟨k, R⟩ : Mat A))) := by
  have h2 := Mat.mvN_reindex (reshuffleL n m k)
    (kronMat P (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Q 0 0 R)))
  rw [reindex_kron_sum_eq n m k P Q R] at h2
  show Mat.MvN
    (⟨n * (m + k), kronMat P (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Q 0 0 R))⟩ : Mat A)
    (⟨n * m + n * k, Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (kronMat P Q) 0 0 (kronMat P R))⟩ : Mat A)
  exact h2

lemma mvN_sum_kron {A : Type} [Ring A] (n m k : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (Q : Matrix (Fin m) (Fin m) A) (R : Matrix (Fin k) (Fin k) A) :
    Mat.MvN (Mat.kron (Mat.sum (⟨n, P⟩ : Mat A) (⟨m, Q⟩ : Mat A)) (⟨k, R⟩ : Mat A))
      (Mat.sum (Mat.kron (⟨n, P⟩ : Mat A) (⟨k, R⟩ : Mat A))
        (Mat.kron (⟨m, Q⟩ : Mat A) (⟨k, R⟩ : Mat A))) := by
  have h2 := Mat.mvN_reindex (reshuffleR n m k)
    (kronMat (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P 0 0 Q)) R)
  rw [reindex_sum_kron_eq n m k P Q R] at h2
  show Mat.MvN
    (⟨(n + m) * k, kronMat (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P 0 0 Q)) R⟩ : Mat A)
    (⟨n * k + m * k, Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (kronMat P R) 0 0 (kronMat Q R))⟩ : Mat A)
  exact h2

/-- The Kronecker product distributes over block sums, up to Murray–von Neumann equivalence:
`p ⊗ (q ⊕ r) ~ (p ⊗ q) ⊕ (p ⊗ r)` and `(p ⊕ q) ⊗ r ~ (p ⊗ r) ⊕ (q ⊗ r)`.  No hypotheses on
`p, q, r` are needed. -/
theorem mvN_additive :
    (∀ (A : Type) [Ring A] (p q r : Mat A),
      Mat.MvN (p.kron (q.sum r)) ((p.kron q).sum (p.kron r))) ∧
    (∀ (A : Type) [Ring A] (p q r : Mat A),
      Mat.MvN ((p.sum q).kron r) ((p.kron r).sum (q.kron r))) := by
  constructor
  · intro A _ p q r
    obtain ⟨n, P⟩ := p
    obtain ⟨m, Q⟩ := q
    obtain ⟨k, R⟩ := r
    exact mvN_kron_sum n m k P Q R
  · intro A _ p q r
    obtain ⟨n, P⟩ := p
    obtain ⟨m, Q⟩ := q
    obtain ⟨k, R⟩ := r
    exact mvN_sum_kron n m k P Q R

end Work.KT

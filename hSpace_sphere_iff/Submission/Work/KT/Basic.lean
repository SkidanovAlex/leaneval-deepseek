import Mathlib
import Submission.Work.KT.Defs

/-!
# Foundations for `K₀`: Kronecker products and the Murray–von Neumann calculus

Helper lemmas about the matrix model of `K₀` (`Submission/Work/KT/Defs.lean`) used by
`Work.KT.k0_basic` and its sub-lemmas.

* `kronMatR` — Kronecker product of rectangular matrices, reindexed to `Fin (n*n') × Fin (m*m')`.
* `Mat.mvN_reindex` — a matrix and its reindexing are Murray–von Neumann equivalent.
* idempotency of `Mat.sum`/`Mat.kron`, and the elementary `cls` lemmas.
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## Rectangular Kronecker products -/

/-- Rectangular Kronecker product, reindexed to `Fin (n * n')`, `Fin (m * m')`. -/
def kronMatR {A : Type} [Mul A] {n m n' m' : ℕ}
    (M : Matrix (Fin n) (Fin m) A) (N : Matrix (Fin n') (Fin m') A) :
    Matrix (Fin (n * n')) (Fin (m * m')) A :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) M N)

/-- `Mat.kron` is the rectangular Kronecker product. -/
lemma Mat.kron_snd {A : Type} [Ring A] (p q : Mat A) : (p.kron q).2 = kronMatR p.2 q.2 := rfl

@[simp]
lemma kronMatR_apply {A : Type} [Mul A] {n m n' m' : ℕ}
    (M : Matrix (Fin n) (Fin m) A) (N : Matrix (Fin n') (Fin m') A)
    (i : Fin n) (i' : Fin n') (j : Fin m) (j' : Fin m') :
    kronMatR M N (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j')) = M i j * N i' j' := by
  simp [kronMatR, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

/-- Reindexing is multiplicative: `reindex` is an algebra isomorphism (rows/cols transported
separately). -/
lemma reindexMul {A : Type} [AddCommMonoid A] [Mul A]
    {m m' n n' p p' : Type} [Fintype n] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (g : p ≃ p') (X : Matrix m n A) (Y : Matrix n p A) :
    Matrix.reindex e f X * Matrix.reindex f g Y = Matrix.reindex e g (X * Y) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv X Y e.symm f.symm g.symm

/-- `(A⊗A')(B⊗B') = (AB)⊗(A'B')` over a commutative ring (assumed as a hypothesis). -/
lemma kroneckerMap_mul {A : Type} [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    {l m n l' m' n' : Type} [Fintype m] [Fintype m']
    (M : Matrix l m A) (N : Matrix m n A) (M' : Matrix l' m' A) (N' : Matrix m' n' A) :
    Matrix.kroneckerMap (· * ·) (M * N) (M' * N') =
      Matrix.kroneckerMap (· * ·) M M' * Matrix.kroneckerMap (· * ·) N N' := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hcomm }
  exact Matrix.mul_kronecker_mul M N M' N'

/-- Multiplicativity of the rectangular Kronecker product. -/
lemma kronMatR_mul {A : Type} [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    {n m k n' m' k' : ℕ}
    (M : Matrix (Fin n) (Fin m) A) (N : Matrix (Fin m) (Fin k) A)
    (M' : Matrix (Fin n') (Fin m') A) (N' : Matrix (Fin m') (Fin k') A) :
    kronMatR (M * N) (M' * N') = kronMatR M M' * kronMatR N N' := by
  unfold kronMatR
  rw [reindexMul]
  congr 1
  exact kroneckerMap_mul hcomm M N M' N'

/-! ## Block sums -/

lemma Mat.sum_snd {A : Type} [Ring A] (p q : Mat A) :
    (p.sum q).2 =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.2 0 0 q.2) := rfl

@[simp]
lemma Mat.sum_apply_inl {A : Type} [Ring A] (p q : Mat A) (i j : Fin p.1) :
    (p.sum q).2 (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = p.2 i j := by
  simp [Mat.sum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks]

@[simp]
lemma Mat.sum_apply_inr {A : Type} [Ring A] (p q : Mat A) (i j : Fin q.1) :
    (p.sum q).2 (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = q.2 i j := by
  simp [Mat.sum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks]

@[simp]
lemma Mat.sum_apply_inl_inr {A : Type} [Ring A] (p q : Mat A) (i : Fin p.1) (j : Fin q.1) :
    (p.sum q).2 (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = 0 := by
  simp [Mat.sum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks]

@[simp]
lemma Mat.sum_apply_inr_inl {A : Type} [Ring A] (p q : Mat A) (i : Fin q.1) (j : Fin p.1) :
    (p.sum q).2 (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
  simp [Mat.sum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks]

/-- A block sum of idempotents is idempotent. -/
lemma Mat.sum_idem {A : Type} [Ring A] {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    (p.sum q).IsIdem := by
  have h : (p.sum q).2 * (p.sum q).2 = (p.sum q).2 := by
    rw [Mat.sum]
    rw [reindexMul]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [show p.2 * p.2 = p.2 from hp, show q.2 * q.2 = q.2 from hq]
  exact h

/-- A Kronecker product of idempotents is idempotent (over a commutative ring). -/
lemma Mat.kron_idem {A : Type} [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) : (p.kron q).IsIdem := by
  change kronMatR p.2 q.2 * kronMatR p.2 q.2 = kronMatR p.2 q.2
  rw [← kronMatR_mul hcomm, show p.2 * p.2 = p.2 from hp, show q.2 * q.2 = q.2 from hq]

/-! ## Reindexing and Murray–von Neumann equivalence -/

/-- A matrix and its reindexing along a bijection of `Fin` types are MvN equivalent. -/
lemma Mat.mvN_reindex {A : Type} [Ring A] {n m : ℕ} (e : Fin n ≃ Fin m)
    (M : Matrix (Fin n) (Fin n) A) :
    Mat.MvN ⟨n, M⟩ ⟨m, Matrix.reindex e e M⟩ := by
  have h1 : (1 : Matrix (Fin n) (Fin n) A).submatrix id (⇑e.symm)
      * M.submatrix (⇑e.symm) id = M := by
    rw [← Matrix.submatrix_mul (1 : Matrix (Fin n) (Fin n) A) M id (⇑e.symm) id
      e.symm.bijective]
    simp
  have h2 : M.submatrix (⇑e.symm) id
      * (1 : Matrix (Fin n) (Fin n) A).submatrix id (⇑e.symm) = Matrix.reindex e e M := by
    rw [← Matrix.submatrix_mul M (1 : Matrix (Fin n) (Fin n) A) (⇑e.symm) id (⇑e.symm)
      Function.bijective_id]
    simp [Matrix.reindex_apply]
  exact ⟨M.submatrix (⇑e.symm) id,
    (1 : Matrix (Fin n) (Fin n) A).submatrix id (⇑e.symm), h1, h2⟩

lemma Mat.mvN_refl {A : Type} [Ring A] {p : Mat A} (hp : p.IsIdem) : p.MvN p :=
  ⟨p.2, p.2, hp, hp⟩

lemma Mat.mvN_symm {A : Type} [Ring A] {p q : Mat A} (h : p.MvN q) : q.MvN p := by
  obtain ⟨a, b, hba, hab⟩ := h
  exact ⟨b, a, hab, hba⟩

lemma Mat.mvN_trans {A : Type} [Ring A] {p q r : Mat A} (hp : p.IsIdem) (hq : q.IsIdem)
    (hr : r.IsIdem) (hpq : p.MvN q) (hqr : q.MvN r) : p.MvN r := by
  obtain ⟨a₁, b₁, h₁, h₁'⟩ := hpq
  obtain ⟨a₂, b₂, h₂, h₂'⟩ := hqr
  refine ⟨a₂ * a₁, b₁ * b₂, ?_, ?_⟩
  · have hQ : b₁ * b₂ * (a₂ * a₁) = b₁ * q.2 * a₁ := by
      rw [Matrix.mul_assoc b₁ b₂ (a₂ * a₁), ← Matrix.mul_assoc b₂ a₂ a₁,
        ← Matrix.mul_assoc b₁ (b₂ * a₂) a₁, h₂]
    rw [hQ, ← h₁', ← Matrix.mul_assoc b₁ a₁ b₁, Matrix.mul_assoc (b₁ * a₁) b₁ a₁,
      h₁, hp]
  · have hQ : a₂ * a₁ * (b₁ * b₂) = a₂ * q.2 * b₂ := by
      rw [Matrix.mul_assoc a₂ a₁ (b₁ * b₂), ← Matrix.mul_assoc a₁ b₁ b₂,
        ← Matrix.mul_assoc a₂ (a₁ * b₁) b₂, h₁']
    rw [hQ, ← h₂, ← Matrix.mul_assoc a₂ b₂ a₂, Matrix.mul_assoc (a₂ * b₂) a₂ b₂,
      h₂', hr]

/-! ## `Mat.map` -/

lemma Mat.map_id {A : Type} [Ring A] (p : Mat A) : p.map (RingHom.id A) = p := by
  obtain ⟨n, M⟩ := p
  simp [Mat.map]

lemma Mat.map_comp {A B C : Type} [Ring A] [Ring B] [Ring C]
    (f : A →+* B) (g : B →+* C) (p : Mat A) :
    p.map (g.comp f) = (p.map f).map g := by
  obtain ⟨n, M⟩ := p
  simp only [Mat.map, Matrix.map_map]
  rfl

lemma Mat.map_idem {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {p : Mat A}
    (hp : p.IsIdem) : (p.map φ).IsIdem := by
  unfold Mat.IsIdem Mat.map at *
  rw [← Matrix.map_mul, hp]

lemma Mat.map_kron {A B : Type} [Ring A] [Ring B] (φ : A →+* B) (p q : Mat A) :
    (p.kron q).map φ = (p.map φ).kron (q.map φ) := by
  obtain ⟨n, M⟩ := p
  obtain ⟨k, N⟩ := q
  change (⟨n * k, (kronMatR M N).map φ⟩ : Mat B) = ⟨n * k, kronMatR (M.map φ) (N.map φ)⟩
  congr 1
  ext i j
  simp [kronMatR, Matrix.reindex_apply, Matrix.map_apply, Matrix.kroneckerMap_apply]

/-! ## Elementary properties of `cls` -/

lemma cls_eq_of_mvN {A : Type} [Ring A] {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem)
    (h : p.MvN q) : cls p = cls q := by
  have hmem : FreeAbelianGroup.of p - FreeAbelianGroup.of q ∈ K0Rel A :=
    AddSubgroup.subset_closure (Or.inl (Or.inr ⟨p, q, hp, hq, h, rfl⟩))
  have hzero : (cls p - cls q : K0 A) = 0 := by
    unfold cls
    rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
    exact hmem
  rwa [sub_eq_zero] at hzero

lemma cls_sum {A : Type} [Ring A] {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    cls (p.sum q) = cls p + cls q := by
  have hmem : FreeAbelianGroup.of (p.sum q) - (FreeAbelianGroup.of p + FreeAbelianGroup.of q)
      ∈ K0Rel A := by
    rw [sub_add_eq_sub_sub]
    exact AddSubgroup.subset_closure (Or.inl (Or.inl ⟨p, q, hp, hq, rfl⟩))
  have hzero : (cls (p.sum q) - (cls p + cls q) : K0 A) = 0 := by
    unfold cls
    rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
    exact hmem
  rwa [sub_eq_zero] at hzero

lemma cls_of_not_idem {A : Type} [Ring A] {p : Mat A} (hp : ¬ p.IsIdem) : cls p = 0 := by
  unfold cls
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure (Or.inr ⟨p, hp, rfl⟩)

end

end Work.KT

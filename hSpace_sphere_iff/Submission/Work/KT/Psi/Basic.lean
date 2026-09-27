import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.map_cls_uncond

/-!
# `Work.KT.Psi.Basic` — infrastructure for the Adams operations `ψ²`, `ψ³` on `K₀`

This file collects the elementary lemmas used by `Work.KT.psi_exists`:

* basic `K₀` lemmas (`cls` of `MvN`-equivalent idempotents, additivity, vanishing on
  non-idempotents, generation by the classes of matrices, `K0.map` on generators);
* transport of `cls` along a reindexing of the index set (used to compute
  `sq2Part`/`cubePart` on product index types);
* the "unreindexed" versions `sq2PartP`, `cubePartP` of the symmetric-power projectors, together
  with the bridges back to the definitions in `Submission.Work.KT.Defs`.
-/

namespace Work.KT

open Matrix

noncomputable section

variable {R S : Type} [Ring R] [Ring S]

/-! ## Elementary `K₀` lemmas -/

theorem cls_eq_of_MvN {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    cls p = cls q := by
  have hmem : FreeAbelianGroup.of p - FreeAbelianGroup.of q ∈ K0Rel R :=
    AddSubgroup.subset_closure (Or.inl (Or.inr ⟨p, q, hp, hq, h, rfl⟩))
  unfold cls
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simpa using hmem

theorem cls_sum {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) : cls (p.sum q) = cls p + cls q := by
  have hmem : FreeAbelianGroup.of (p.sum q) - FreeAbelianGroup.of p - FreeAbelianGroup.of q ∈
      K0Rel R :=
    AddSubgroup.subset_closure (Or.inl (Or.inl ⟨p, q, hp, hq, rfl⟩))
  have hzero : cls (p.sum q) - (cls p + cls q) = 0 := by
    unfold cls
    rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
    simpa [sub_sub] using hmem
  exact sub_eq_zero.mp hzero

theorem cls_zero_of_not_idem {p : Mat R} (hp : ¬ p.IsIdem) : cls p = 0 := by
  have hmem : FreeAbelianGroup.of p ∈ K0Rel R :=
    AddSubgroup.subset_closure (Or.inr ⟨p, hp, rfl⟩)
  unfold cls
  rw [QuotientAddGroup.eq_zero_iff]
  simpa using hmem

theorem cls_closure_top : AddSubgroup.closure (Set.range (cls : Mat R → K0 R)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine QuotientAddGroup.induction_on x ?_
  intro a
  suffices key : (QuotientAddGroup.mk a : K0 R) ∈
      AddSubgroup.closure (Set.range (cls : Mat R → K0 R)) from key
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simpa using AddSubgroup.zero_mem
      (AddSubgroup.closure (Set.range (cls : Mat R → K0 R)) : AddSubgroup (K0 R))
  · intro p; exact AddSubgroup.subset_closure ⟨p, rfl⟩
  · intro p hp; simpa using AddSubgroup.neg_mem _ hp
  · intro p q hp hq; simpa using AddSubgroup.add_mem _ hp hq

theorem addHom_ext_cls {M : Type} [AddCommGroup M] {f g : K0 R →+ M}
    (h : ∀ p : Mat R, f (cls p) = g (cls p)) : f = g := by
  refine AddMonoidHom.ext (fun x => ?_)
  have hmem : x ∈ AddSubgroup.closure (Set.range (cls : Mat R → K0 R)) := by
    rw [cls_closure_top]; trivial
  exact AddSubgroup.closure_induction (p := fun y _ => f y = g y)
    (fun y hy => by obtain ⟨p, rfl⟩ := hy; exact h p)
    (by simp)
    (fun a b _ _ iha ihb => by simp [map_add, iha, ihb])
    (fun a _ iha => by simp [map_neg, iha])
    hmem

theorem addHom₂_ext_cls {M : Type} [AddCommGroup M] {F G : K0 R →+ K0 R →+ M}
    (h : ∀ p q : Mat R, F (cls p) (cls q) = G (cls p) (cls q)) : F = G := by
  have h1 : ∀ p : Mat R, F (cls p) = G (cls p) := fun p => addHom_ext_cls (fun q => h p q)
  exact addHom_ext_cls h1

/-! ## Reindexing of index sets

`cls` is invariant under conjugating a matrix by a permutation of its index set.  The permutation
is realised by a rectangular "partial permutation matrix" so that Murray–von Neumann equivalence
can be exhibited directly. -/

/-- The rectangular permutation matrix of `τ : Fin n ≃ Fin n'`: it maps `Fin n` to `Fin n'`. -/
def pmat (R : Type) [Ring R] {n n' : ℕ} (τ : Fin n ≃ Fin n') : Matrix (Fin n') (Fin n) R :=
  fun i j => if τ j = i then 1 else 0

theorem pmat_mul_rect (R : Type) [Ring R] {n n' m : ℕ} (τ : Fin n ≃ Fin n')
    (Y : Matrix (Fin n) (Fin m) R) : pmat R τ * Y = Y.submatrix τ.symm id := by
  ext i j
  simp only [Matrix.mul_apply, pmat, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single (τ.symm i)]
  · rw [if_pos (τ.apply_symm_apply i), one_mul]
  · intro b _ hb
    rw [if_neg (fun h => hb ((Equiv.eq_symm_apply τ).mpr h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rect_mul_pmat (R : Type) [Ring R] {n n' m : ℕ} (τ : Fin n ≃ Fin n')
    (Z : Matrix (Fin m) (Fin n') R) : Z * pmat R τ = Z.submatrix id τ := by
  ext i j
  simp only [Matrix.mul_apply, pmat, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single (τ j)]
  · rw [if_pos rfl, mul_one]
  · intro b _ hb; rw [if_neg (fun h => hb h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rect_mul_pmat_trans (R : Type) [Ring R] {n m : ℕ} {n' : ℕ} (τ : Fin n ≃ Fin n')
    (Z : Matrix (Fin m) (Fin n) R) : Z * (pmat R τ)ᵀ = Z.submatrix id τ.symm := by
  ext i j
  simp only [Matrix.mul_apply, pmat, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single (τ.symm j)]
  · rw [if_pos (τ.apply_symm_apply j), mul_one]
  · intro b _ hb
    rw [if_neg (fun h => hb ((Equiv.eq_symm_apply τ).mpr h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pmat_trans_mul (R : Type) [Ring R] {n n' : ℕ} (τ : Fin n ≃ Fin n') :
    (pmat R τ)ᵀ * pmat R τ = 1 := by
  rw [rect_mul_pmat R τ (pmat R τ)ᵀ]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, pmat, Matrix.one_apply, id_eq]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun hh => h (τ.injective hh)), if_neg h]

theorem pmat_mul_pmat_trans (R : Type) [Ring R] {n n' : ℕ} (τ : Fin n ≃ Fin n')
    (X : Matrix (Fin n) (Fin n) R) :
    pmat R τ * X * (pmat R τ)ᵀ = Matrix.reindex τ τ X := by
  rw [pmat_mul_rect, rect_mul_pmat_trans]; rfl

theorem reindex_mul_self {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (X : Matrix ι ι R) :
    Matrix.reindex e e (X * X) = Matrix.reindex e e X * Matrix.reindex e e X :=
  map_mul (Matrix.reindexRingEquiv R e) X X

theorem reindex_reindex {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]
    (e₁ : ι ≃ κ) (e₂ : κ ≃ ν) (M : Matrix ι ι R) :
    Matrix.reindex e₂ e₂ (Matrix.reindex e₁ e₁ M) = Matrix.reindex (e₁.trans e₂) (e₁.trans e₂) M := by
  rw [← Matrix.reindex_trans]; rfl

/-- Reassociation of a product of four rectangular matrices. -/
theorem mul_assoc4 {a b c d e : Type} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (D : Matrix d e R) :
    A * B * (C * D) = A * (B * C) * D := by
  rw [Matrix.mul_assoc A B (C * D), ← Matrix.mul_assoc B C D, ← Matrix.mul_assoc A (B * C) D]

/-- `cls` is invariant under reindexing a square matrix by a permutation of `Fin n`. -/
theorem cls_reindex_perm (R : Type) [Ring R] {n n' : ℕ} (X : Matrix (Fin n) (Fin n) R)
    (hX : X * X = X) (τ : Fin n ≃ Fin n') :
    cls (⟨n, X⟩ : Mat R) = cls ⟨n', Matrix.reindex τ τ X⟩ := by
  have hY : Matrix.reindex τ τ X * Matrix.reindex τ τ X = Matrix.reindex τ τ X := by
    rw [← reindex_mul_self, hX]
  have hb : X * (pmat R τ)ᵀ * (pmat R τ * X) = X := by
    rw [mul_assoc4, pmat_trans_mul, Matrix.mul_one, hX]
  have ha : pmat R τ * X * (X * (pmat R τ)ᵀ) = Matrix.reindex τ τ X := by
    rw [mul_assoc4, hX, pmat_mul_pmat_trans]
  exact cls_eq_of_MvN hX hY ⟨pmat R τ * X, X * (pmat R τ)ᵀ, hb, ha⟩

/-! ### `Mat` of an arbitrary finite index type -/

/-- A square matrix over `ι` packaged as an element of `Mat R`, using a bijection `ι ≃ Fin n`. -/
def Mat.ofIdx {ι : Type} (M : Matrix ι ι R) (n : ℕ) (e : ι ≃ Fin n) : Mat R :=
  ⟨n, Matrix.reindex e e M⟩

/-- The class of a square matrix over an arbitrary index type. -/
def clsE {ι : Type} (M : Matrix ι ι R) (n : ℕ) (e : ι ≃ Fin n) : K0 R :=
  cls (Mat.ofIdx M n e)

theorem clsE_wellDefined {ι : Type} [Fintype ι] {M : Matrix ι ι R} (hM : M * M = M)
    {n n' : ℕ} (e : ι ≃ Fin n) (e' : ι ≃ Fin n') : clsE M n e = clsE M n' e' := by
  have hidem : Matrix.reindex e e M * Matrix.reindex e e M = Matrix.reindex e e M := by
    rw [← reindex_mul_self, hM]
  have hτ : e.trans (e.symm.trans e') = e' := by
    ext x; simp [Equiv.trans_apply]
  have h2 : Matrix.reindex (e.symm.trans e') (e.symm.trans e') (Matrix.reindex e e M) =
      Matrix.reindex e' e' M := by
    rw [reindex_reindex, hτ]
  have h3 : Matrix.reindex (e.symm.trans e') (e.symm.trans e') (Matrix.reindex e e M) =
      Matrix.reindex e' e' M := h2
  simp only [clsE, Mat.ofIdx]
  rw [← h3]
  exact cls_reindex_perm R (Matrix.reindex e e M) hidem (e.symm.trans e')

/-- `clsE` of a reindexed matrix: the index equivalence can be pushed through. -/
theorem clsE_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι ι R) (n : ℕ)
    (e : ι ≃ Fin n) (g : ι ≃ κ) :
    clsE (Matrix.reindex g g M) n (g.symm.trans e) = clsE M n e := by
  have h1 : g.trans (g.symm.trans e) = e := by ext x; simp [Equiv.trans_apply]
  have h2 : Matrix.reindex (g.symm.trans e) (g.symm.trans e) (Matrix.reindex g g M) =
      Matrix.reindex e e M := by
    rw [reindex_reindex, h1]
  simp only [clsE, Mat.ofIdx]
  rw [h2]

/-! ### `Matrix.reindex` versus `permMatrix` -/

theorem permMatrix_apply' {ι : Type} [DecidableEq ι] (σ : Equiv.Perm ι) (i j : ι) :
    σ.permMatrix R i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp

theorem reindex_permMatrix {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (σ : Equiv.Perm ι) :
    Matrix.reindex e e (Equiv.Perm.permMatrix R σ) =
      Equiv.Perm.permMatrix R (e.symm.trans (σ.trans e)) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, permMatrix_apply', permMatrix_apply']
  by_cases h : σ (e.symm i) = e.symm j
  · have h' : (e.symm.trans (σ.trans e)) i = j := by
      simp only [Equiv.trans_apply]; exact (Equiv.eq_symm_apply e).mp h
    rw [if_pos h, if_pos h']
  · have h' : ¬ ((e.symm.trans (σ.trans e)) i = j) := by
      intro hh
      exact h ((Equiv.eq_symm_apply e).mpr (by simpa only [Equiv.trans_apply] using hh))
    rw [if_neg h, if_neg h']


/-! ## The unreindexed symmetric / exterior and cyclically-invariant parts -/

section Adams

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The cyclic permutation `((i,j),k) ↦ ((k,i),j)` of `Fin n × Fin n × Fin n`. -/
def cycPermP (n : ℕ) : Equiv.Perm ((Fin n × Fin n) × Fin n) where
  toFun x := ((x.2, x.1.1), x.1.2)
  invFun x := ((x.1.2, x.2), x.1.1)
  left_inv x := by simp
  right_inv x := by simp

/-- The reindexing equivalence `Fin (n*n*n) ≃ (Fin n × Fin n) × Fin n` used to define `cycPerm`. -/
def cycIdx (n : ℕ) : Fin (n * n * n) ≃ (Fin n × Fin n) × Fin n :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))

/-- `p ⊗ p` cut down by `(1 + ε·swap)/2`, on the product index type `Fin n × Fin n`. -/
def sq2PartP (ε : ℂ) (p : Mat A) : Matrix (Fin p.1 × Fin p.1) (Fin p.1 × Fin p.1) A :=
  kroneckerMap (· * ·) p.2 p.2 *
    (algebraMap ℂ A (1 / 2) •
      (1 + algebraMap ℂ A ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1))))

/-- `p ⊗ p ⊗ p` cut down by the spectral projector of the cyclic permutation, on the product
index type `(Fin n × Fin n) × Fin n`. -/
def cubePartP (lam : ℂ) (p : Mat A) :
    Matrix ((Fin p.1 × Fin p.1) × Fin p.1) ((Fin p.1 × Fin p.1) × Fin p.1) A :=
  kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2 *
    (algebraMap ℂ A (1 / 3) •
      (1 + algebraMap ℂ A lam⁻¹ • Equiv.Perm.permMatrix A (cycPermP p.1) +
        algebraMap ℂ A (lam⁻¹ ^ 2) •
          (Equiv.Perm.permMatrix A (cycPermP p.1) *
            Equiv.Perm.permMatrix A (cycPermP p.1))))

theorem reindex_smul (c : A) {ι κ : Type} (e : ι ≃ κ) (X : Matrix ι ι A) :
    Matrix.reindex e e (c • X) = c • Matrix.reindex e e X := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]

theorem reindex_mul' {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (X Y : Matrix ι ι A) :
    Matrix.reindex e e (X * Y) = Matrix.reindex e e X * Matrix.reindex e e Y :=
  map_mul (Matrix.reindexRingEquiv A e) X Y

theorem reindex_add' {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (X Y : Matrix ι ι A) :
    Matrix.reindex e e (X + Y) = Matrix.reindex e e X + Matrix.reindex e e Y :=
  map_add (Matrix.reindexRingEquiv A e) X Y

theorem reindex_one' {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) : Matrix.reindex e e (1 : Matrix ι ι A) = 1 := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun hh => h (e.symm.injective hh)), if_neg h]

theorem reindex_permMatrix_prodComm (n : ℕ) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n))) =
      Equiv.Perm.permMatrix A (swapPerm n) := by
  rw [reindex_permMatrix]
  congr 1

theorem reindex_permMatrix_cyc (n : ℕ) :
    Matrix.reindex (cycIdx n).symm (cycIdx n).symm
      (Equiv.Perm.permMatrix A (cycPermP n)) =
      Equiv.Perm.permMatrix A (cycPerm n) := by
  rw [reindex_permMatrix]
  congr 1

theorem cycIdx_symm_eq (n : ℕ) :
    (cycIdx n).symm =
      (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin n))).trans finProdFinEquiv := by
  ext x
  simp only [cycIdx, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.prodCongr_symm, Equiv.refl_symm]

theorem kronMat_kronMat_eq (p : Mat A) :
    Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm
        (kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2) =
      kronMat (kronMat p.2 p.2) p.2 := by
  change Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm
        (kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (kroneckerMap (· * ·) (kronMat p.2 p.2) p.2)
  rw [show kronMat p.2 p.2 = Matrix.reindex finProdFinEquiv finProdFinEquiv
      (kroneckerMap (· * ·) p.2 p.2) from rfl]
  rw [kroneckerMap_reindex_left, reindex_reindex, cycIdx_symm_eq]

theorem sq2Part_reindex (ε : ℂ) (p : Mat A) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (sq2PartP ε p) =
      kronMat p.2 p.2 *
        (algebraMap ℂ A (1 / 2) •
          (1 + algebraMap ℂ A ε • Equiv.Perm.permMatrix A (swapPerm p.1))) := by
  simp only [sq2PartP, reindex_mul', reindex_add', reindex_one', reindex_smul,
    reindex_permMatrix_prodComm]
  rfl

theorem cubePart_reindex (lam : ℂ) (p : Mat A) :
    Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm (cubePartP lam p) =
      kronMat (kronMat p.2 p.2) p.2 *
        (algebraMap ℂ A (1 / 3) •
          (1 + algebraMap ℂ A lam⁻¹ • Equiv.Perm.permMatrix A (cycPerm p.1) +
            algebraMap ℂ A (lam⁻¹ ^ 2) •
              (Equiv.Perm.permMatrix A (cycPerm p.1) *
                Equiv.Perm.permMatrix A (cycPerm p.1)))) := by
  simp only [cubePartP, reindex_mul', reindex_add', reindex_one', reindex_smul,
    reindex_permMatrix_cyc]
  rw [kronMat_kronMat_eq]

/-- `sq2Part` in terms of the unreindexed version `sq2PartP`. -/
theorem sq2Part_eq (ε : ℂ) (p : Mat A) :
    sq2Part ε p =
      ⟨p.1 * p.1, Matrix.reindex finProdFinEquiv finProdFinEquiv (sq2PartP ε p)⟩ := by
  rw [sq2Part_reindex]
  rfl

/-- `cubePart` in terms of the unreindexed version `cubePartP`. -/
theorem cubePart_eq (lam : ℂ) (p : Mat A) :
    cubePart lam p =
      ⟨p.1 * p.1 * p.1, Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm (cubePartP lam p)⟩ := by
  rw [cubePart_reindex]
  rfl

theorem cls_sq2PartP (ε : ℂ) (p : Mat A) :
    clsE (sq2PartP ε p) (p.1 * p.1) finProdFinEquiv = cls (sq2Part ε p) := by
  rw [sq2Part_eq]
  rfl

theorem cls_cubePartP (lam : ℂ) (p : Mat A) :
    clsE (cubePartP lam p) (p.1 * p.1 * p.1) (cycIdx p.1).symm = cls (cubePart lam p) := by
  rw [cubePart_eq]
  rfl

end Adams

end

/-! ## More elementary `Mat` / `K₀` lemmas -/

section More

variable {A : Type} [Ring A]

theorem Mat.isIdem_sum {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) : (p.sum q).IsIdem := by
  unfold Mat.IsIdem Mat.sum at *
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hp, hq]

theorem Mat.isIdem_map {B : Type} [Ring B] {p : Mat A} (hp : p.IsIdem) (φ : A →+* B) :
    (p.map φ).IsIdem := by
  unfold Mat.IsIdem Mat.map at *
  simp only
  rw [← Matrix.map_mul, hp]

theorem kron_mul (hA : ∀ x y : A, x * y = y * x) {m m' : ℕ}
    (M N : Matrix (Fin m) (Fin m) A) (P Q : Matrix (Fin m') (Fin m') A) :
    kroneckerMap (· * ·) (M * N) (P * Q) =
      kroneckerMap (· * ·) M P * kroneckerMap (· * ·) N Q := by
  letI : CommSemiring A := { ‹Ring A› with mul_comm := fun a b => hA a b }
  exact Matrix.mul_kronecker_mul M N P Q

theorem Mat.isIdem_kron (hA : ∀ x y : A, x * y = y * x) {p q : Mat A} (hp : p.IsIdem)
    (hq : q.IsIdem) : (p.kron q).IsIdem := by
  have hmul : Matrix.reindex finProdFinEquiv finProdFinEquiv
        (kroneckerMap (· * ·) p.2 q.2 * kroneckerMap (· * ·) p.2 q.2) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (kroneckerMap (· * ·) p.2 q.2) *
        Matrix.reindex finProdFinEquiv finProdFinEquiv (kroneckerMap (· * ·) p.2 q.2) :=
    map_mul (Matrix.reindexRingEquiv A finProdFinEquiv) _ _
  unfold Mat.IsIdem Mat.kron kronMat
  simp only
  rw [← hmul, ← kron_mul hA, hp, hq]

theorem cls_map_of_idem {B : Type} [Ring B] (φ : A →+* B) {p : Mat A} (hp : p.IsIdem) :
    K0.map φ (cls p) = cls (p.map φ) := by
  rw [map_cls_uncond]
  unfold mapCls
  rw [if_pos hp]

end More

/-! ## A primitive cube root of unity -/

theorem omega_pow_three : omega ^ 3 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have h : (3 : ℕ) * (2 * Real.pi * Complex.I / 3) = 2 * Real.pi * Complex.I := by ring
  rw [h, Complex.exp_two_pi_mul_I]

theorem omega_ne_zero : omega ≠ 0 := Complex.exp_ne_zero _

theorem omega_mul_sq : omega * omega ^ 2 = 1 := by
  have h : omega * omega ^ 2 = omega ^ (1 + 2) := by rw [pow_add, pow_one]
  rw [h, show (1 : ℕ) + 2 = 3 from rfl, omega_pow_three]

theorem omega_inv : omega⁻¹ = omega ^ 2 :=
  inv_eq_of_mul_eq_one_left (by rw [mul_comm]; exact omega_mul_sq)

theorem omega_sq_inv : omega ^ 2 = omega⁻¹ := omega_inv.symm

theorem omega_inv_sq : (omega⁻¹) ^ 2 = omega := by
  rw [omega_inv, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, omega_pow_three, one_mul,
    pow_one]


end Work.KT

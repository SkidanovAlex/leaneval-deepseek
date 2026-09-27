import Mathlib
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Basic

/-!
# `Work.KT.Psi.K3` — infrastructure for `psi3Cls_kron`

Multiplicativity of `ψ³` on generators rests on the tensor decomposition

`(p ⊗ q) ⊗ (p ⊗ q) ⊗ (p ⊗ q) ≅ (p ⊗ p ⊗ p) ⊗ (q ⊗ q ⊗ q)`

together with the factorisation of the order-three spectral projector

`(1 + λ⁻¹ w + λ⁻² w²)/3 = Σ_{λ₁λ₂=λ} (1+λ₁⁻¹c₁+λ₁⁻²c₁²)/3 ⊗ (1+λ₂⁻¹c₂+λ₂⁻²c₂²)/3`

for `w = c₁ ⊗ c₂`.  This file collects the definitions (`TZ`, `PM`, `SH`) and the elementary
lemmas about them.
-/

namespace Work.KT.Psi.K3

open Matrix

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- Index type of the unreindexed triple tensor power. -/
abbrev I3 (n : ℕ) : Type := (Fin n × Fin n) × Fin n

/-- The triple Kronecker power of a square matrix, on `I3 n`. -/
def TZ {n : ℕ} (X : Matrix (Fin n) (Fin n) A) : Matrix (I3 n) (I3 n) A :=
  Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) X X) X

omit [Algebra ℂ A] in
@[simp] theorem TZ_apply {n : ℕ} (X : Matrix (Fin n) (Fin n) A) (x y : I3 n) :
    TZ X x y = (X x.1.1 y.1.1 * X x.1.2 y.1.2) * X x.2 y.2 := rfl

/-- The spectral projector `(1 + λ⁻¹c + λ⁻²c²)/3`. -/
def PM {ι : Type} [Fintype ι] [DecidableEq ι] (u : Matrix ι ι A) (lam : ℂ) : Matrix ι ι A :=
  (1 / 3 : ℂ) • (1 + lam⁻¹ • u + (lam⁻¹) ^ 2 • (u * u))

/-- The shuffle `I3 (n*m) ≃ I3 n × I3 m`. -/
def SH (n m : ℕ) : I3 (n * m) ≃ I3 n × I3 m where
  toFun x :=
    ⟨⟨⟨(finProdFinEquiv.symm x.1.1).1, (finProdFinEquiv.symm x.1.2).1⟩,
        (finProdFinEquiv.symm x.2).1⟩,
      ⟨⟨(finProdFinEquiv.symm x.1.1).2, (finProdFinEquiv.symm x.1.2).2⟩,
        (finProdFinEquiv.symm x.2).2⟩⟩
  invFun y :=
    ⟨⟨finProdFinEquiv (y.1.1.1, y.2.1.1), finProdFinEquiv (y.1.1.2, y.2.1.2)⟩,
      finProdFinEquiv (y.1.2, y.2.2)⟩
  left_inv x := by
    obtain ⟨⟨a, b⟩, c⟩ := x
    refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> exact Equiv.apply_symm_apply _ _
  right_inv y := by
    obtain ⟨⟨⟨a1, b1⟩, c1⟩, ⟨⟨a2, b2⟩, c2⟩⟩ := y
    simp

@[simp] theorem SH_apply (n m : ℕ) (a b c : Fin (n * m)) :
    SH n m ⟨⟨a, b⟩, c⟩ =
      ⟨⟨⟨(finProdFinEquiv.symm a).1, (finProdFinEquiv.symm b).1⟩, (finProdFinEquiv.symm c).1⟩,
        ⟨⟨(finProdFinEquiv.symm a).2, (finProdFinEquiv.symm b).2⟩, (finProdFinEquiv.symm c).2⟩⟩ :=
  rfl

@[simp] theorem SH_symm_apply (n m : ℕ) (a1 b1 c1 : Fin n) (a2 b2 c2 : Fin m) :
    (SH n m).symm ⟨⟨⟨a1, b1⟩, c1⟩, ⟨⟨a2, b2⟩, c2⟩⟩ =
      ⟨⟨finProdFinEquiv (a1, a2), finProdFinEquiv (b1, b2)⟩, finProdFinEquiv (c1, c2)⟩ := by
  rw [Equiv.symm_apply_eq]
  simp [SH_apply]

@[simp] theorem cycPermP_apply (n : ℕ) (x : I3 n) :
    cycPermP n x = ((x.2, x.1.1), x.1.2) := rfl

@[simp] theorem cycPermP_symm_apply (n : ℕ) (x : I3 n) :
    (cycPermP n).symm x = ((x.1.2, x.2), x.1.1) := rfl

theorem cycPermP_cube (n : ℕ) : cycPermP n * cycPermP n * cycPermP n = 1 := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i, j⟩, k⟩ := x
  rfl

theorem permMatrix_cycPermP_cube (n : ℕ) :
    Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n) *
      Equiv.Perm.permMatrix A (cycPermP n) = 1 := by
  have hc : cycPermP n * (cycPermP n * cycPermP n) = 1 := by
    rw [← mul_assoc]; exact cycPermP_cube n
  rw [← Matrix.permMatrix_mul (R := A) (σ := cycPermP n) (τ := cycPermP n)]
  rw [← Matrix.permMatrix_mul (R := A) (σ := cycPermP n) (τ := cycPermP n * cycPermP n)]
  rw [hc, Matrix.permMatrix_one]

omit [Algebra ℂ A] in
theorem kroneckerMap_permMatrix {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (σ : Equiv.Perm ι) (τ : Equiv.Perm κ) :
    Matrix.kroneckerMap (· * ·) (Equiv.Perm.permMatrix A σ) (Equiv.Perm.permMatrix A τ) =
      Equiv.Perm.permMatrix A (Equiv.prodCongr σ τ) := by
  ext i j
  rw [Matrix.kroneckerMap_apply, permMatrix_apply', permMatrix_apply', permMatrix_apply']
  by_cases h1 : σ i.1 = j.1 <;> by_cases h2 : τ i.2 = j.2 <;>
    simp [h1, h2, Equiv.prodCongr_apply, Prod.ext_iff]

-- omega facts
theorem omega_primRoot : IsPrimitiveRoot omega 3 := by
  have h := Complex.isPrimitiveRoot_exp_of_coprime 1 3 (by norm_num) (by norm_num)
  have harg : (2 : ℂ) * ↑Real.pi * Complex.I / 3 =
      2 * ↑Real.pi * Complex.I * (↑(1:ℕ) / ↑(3:ℕ)) := by push_cast; ring
  rw [omega, harg]
  exact h

theorem omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by
  have h : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by
    have : (omega - 1) * (omega ^ 2 + omega + 1) = omega ^ 3 - 1 := by ring
    rw [this, omega_pow_three]; ring
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) (omega_primRoot.ne_one (by norm_num))
  · exact h2

theorem one_add_omega_add_omega_sq : 1 + omega + omega ^ 2 = 0 := by
  linear_combination omega_sq_add_omega_add_one

theorem omega_pow_four : omega ^ 4 = omega := by
  rw [show (4:ℕ) = 3 + 1 from rfl, pow_add, omega_pow_three, one_mul, pow_one]

theorem omega2_inv : (omega ^ 2)⁻¹ = omega := by
  rw [← inv_pow, omega_inv_sq]

theorem omega2_inv_sq : ((omega ^ 2)⁻¹) ^ 2 = omega ^ 2 := by
  rw [omega2_inv]

theorem sum_inv : (1:ℂ)⁻¹ + omega⁻¹ + (omega ^ 2)⁻¹ = 0 := by
  rw [inv_one, omega_inv, omega2_inv]
  linear_combination omega_sq_add_omega_add_one

theorem sum_inv_sq : (1:ℂ)⁻¹ ^ 2 + (omega⁻¹) ^ 2 + ((omega ^ 2)⁻¹) ^ 2 = 0 := by
  rw [inv_one, one_pow, omega_inv_sq, omega2_inv]
  linear_combination one_add_omega_add_omega_sq

-- TZ facts
theorem TZ_mul_self {n : ℕ} (hA : ∀ x y : A, x * y = y * x) (X : Matrix (Fin n) (Fin n) A) :
    TZ X * TZ X = TZ (X * X) := by
  letI : CommSemiring A := { ‹Ring A› with mul_comm := hA }
  show Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) X X) X *
      Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) X X) X = _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

theorem TZ_idem {n : ℕ} (hA : ∀ x y : A, x * y = y * x) (X : Matrix (Fin n) (Fin n) A)
    (hX : X * X = X) : TZ X * TZ X = TZ X := by
  rw [TZ_mul_self hA X, hX]

theorem reindex_cyc_TZ {n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (X : Matrix (Fin n) (Fin n) A) :
    Matrix.reindex (cycPermP n) (cycPermP n) (TZ X) = TZ X := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, TZ_apply, cycPermP_symm_apply]
  ring

-- bridge between ℂ-scalars and A-scalars
theorem smulC_eq_smulA {ι : Type} (c : ℂ) (M : Matrix ι ι A) :
    c • M = algebraMap ℂ A c • M := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Algebra.smul_def]

theorem reindex_smulC {ι κ : Type} (e : ι ≃ κ) (c : ℂ) (X : Matrix ι ι A) :
    Matrix.reindex e e (c • X) = c • Matrix.reindex e e X := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]

theorem PM_eq_algebraMap {ι : Type} [Fintype ι] [DecidableEq ι] (u : Matrix ι ι A) (lam : ℂ) :
    PM u lam = algebraMap ℂ A (1 / 3) •
      (1 + algebraMap ℂ A lam⁻¹ • u + algebraMap ℂ A ((lam⁻¹) ^ 2) • (u * u)) := by
  rw [PM]
  simp only [smulC_eq_smulA]

theorem cubePartP_eq (lam : ℂ) (p : Mat A) :
    cubePartP lam p = TZ p.2 * PM (Equiv.Perm.permMatrix A (cycPermP p.1)) lam := by
  rw [PM_eq_algebraMap]
  rfl

theorem reindex_PM {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (u : Matrix ι ι A) (lam : ℂ) :
    Matrix.reindex e e (PM u lam) = PM (Matrix.reindex e e u) lam := by
  simp only [PM, reindex_smulC, reindex_add', reindex_one', reindex_mul']

-- The flip of the first two tensor factors
/-- The flip `(i,j,k) ↦ (j,i,k)` of the first two tensor factors. -/
def FL (n : ℕ) : Equiv.Perm (I3 n) where
  toFun x := ((x.1.2, x.1.1), x.2)
  invFun x := ((x.1.2, x.1.1), x.2)
  left_inv := by rintro ⟨⟨i, j⟩, k⟩; rfl
  right_inv := by rintro ⟨⟨i, j⟩, k⟩; rfl

@[simp] theorem FL_apply (n : ℕ) (x : I3 n) : FL n x = ((x.1.2, x.1.1), x.2) := rfl
@[simp] theorem FL_symm_apply (n : ℕ) (x : I3 n) : (FL n).symm x = ((x.1.2, x.1.1), x.2) := rfl

theorem FL_conj_cyc (n : ℕ) :
    (FL n).symm.trans ((cycPermP n).trans (FL n)) = cycPermP n * cycPermP n := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i, j⟩, k⟩ := x
  rfl

theorem reindex_FL_TZ {n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (X : Matrix (Fin n) (Fin n) A) :
    Matrix.reindex (FL n) (FL n) (TZ X) = TZ X := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, TZ_apply, FL_symm_apply]
  ring

theorem reindex_FL_permMatrix_cyc (n : ℕ) :
    Matrix.reindex (FL n) (FL n) (Equiv.Perm.permMatrix A (cycPermP n)) =
      Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n) := by
  rw [reindex_permMatrix, FL_conj_cyc, Matrix.permMatrix_mul]

theorem PM_sq_omega {ι : Type} [Fintype ι] [DecidableEq ι] (u : Matrix ι ι A)
    (hu : u * u * u = 1) : PM (u * u) omega = PM u (omega ^ 2) := by
  have h4 : (u * u) * (u * u) = u := by
    rw [← Matrix.mul_assoc (u * u) u u, hu, Matrix.one_mul]
  rw [PM, PM, h4, omega_inv_sq, omega2_inv_sq, omega_inv, omega2_inv]
  congr 1
  abel

theorem cubePartP_conj (hA : ∀ x y : A, x * y = y * x) (p : Mat A) :
    Matrix.reindex (FL p.1) (FL p.1) (cubePartP omega p) = cubePartP (omega ^ 2) p := by
  have hu : Equiv.Perm.permMatrix A (cycPermP p.1) * Equiv.Perm.permMatrix A (cycPermP p.1) *
      Equiv.Perm.permMatrix A (cycPermP p.1) = 1 := permMatrix_cycPermP_cube p.1
  rw [cubePartP_eq, cubePartP_eq, reindex_mul', reindex_FL_TZ hA, reindex_PM,
    reindex_FL_permMatrix_cyc]
  rw [PM_sq_omega (Equiv.Perm.permMatrix A (cycPermP p.1)) hu]

section Cls

variable {R : Type} [Ring R]

@[simp] theorem reindex_refl {ι : Type} (M : Matrix ι ι R) :
    Matrix.reindex (Equiv.refl ι) (Equiv.refl ι) M = M := by
  ext i j
  simp [Matrix.reindex_apply]

theorem cls_kron_of_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    {n m : ℕ} (e₁ : ι ≃ Fin n) (e₂ : κ ≃ Fin m)
    (P : Matrix ι ι R) (Q : Matrix κ κ R) :
    cls (Mat.kron (⟨n, Matrix.reindex e₁ e₁ P⟩ : Mat R) ⟨m, Matrix.reindex e₂ e₂ Q⟩) =
      clsE (Matrix.kroneckerMap (· * ·) P Q) (n * m)
        ((e₁.prodCongr e₂).trans finProdFinEquiv) := by
  have hmat : Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (Matrix.reindex e₁ e₁ P) (Matrix.reindex e₂ e₂ Q)) =
      Matrix.reindex ((e₁.prodCongr e₂).trans finProdFinEquiv)
        ((e₁.prodCongr e₂).trans finProdFinEquiv) (Matrix.kroneckerMap (· * ·) P Q) := by
    rw [Matrix.kroneckerMap_reindex, reindex_reindex]
  simp only [Mat.kron, kronMat, clsE, Mat.ofIdx]
  rw [hmat]

theorem clsE_kron_conj {ι κ ι' : Type} [Fintype ι] [Fintype κ] [Fintype ι']
    (g : ι ≃ ι') (A : Matrix ι ι R) (B : Matrix κ κ R) (n : ℕ) (e : ι' × κ ≃ Fin n) :
    clsE (Matrix.kroneckerMap (· * ·) (Matrix.reindex g g A) B) n e =
      clsE (Matrix.kroneckerMap (· * ·) A B) n ((g.prodCongr (Equiv.refl κ)).trans e) := by
  have hmat : Matrix.reindex e e
        (Matrix.kroneckerMap (· * ·) (Matrix.reindex g g A) B) =
      Matrix.reindex ((g.prodCongr (Equiv.refl κ)).trans e)
        ((g.prodCongr (Equiv.refl κ)).trans e) (Matrix.kroneckerMap (· * ·) A B) := by
    rw [Matrix.kroneckerMap_reindex_left, reindex_reindex]
  simp only [clsE, Mat.ofIdx]
  rw [hmat]

end Cls

end

end Work.KT.Psi.K3

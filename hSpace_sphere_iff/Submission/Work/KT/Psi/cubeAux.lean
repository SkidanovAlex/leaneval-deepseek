import Mathlib
import Submission.Work.KT.Psi.Basic

/-!
# Auxiliary definitions for `Work.KT.Psi.cubePart_conj`

The conjugation lemma `cubePart omega p ~ cubePart (omega^2) p` is proved by conjugating the
cyclic permutation `cycPermP` by the flip of the first two tensor factors.  This file collects the
index-permutation and Kronecker-product infrastructure used by that argument (and by the
idempotency of `cubePartP`).
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type}

/-! ## The flip of the first two tensor factors -/

/-- The flip of the first two tensor factors of `(Fin n × Fin n) × Fin n`, `(i,j,k) ↦ (j,i,k)`. -/
def flipPermP (n : ℕ) : Equiv.Perm ((Fin n × Fin n) × Fin n) where
  toFun x := ((x.1.2, x.1.1), x.2)
  invFun x := ((x.1.2, x.1.1), x.2)
  left_inv x := by rcases x with ⟨⟨i, j⟩, k⟩; rfl
  right_inv x := by rcases x with ⟨⟨i, j⟩, k⟩; rfl

@[simp] theorem flipPermP_apply (n : ℕ) (x : (Fin n × Fin n) × Fin n) :
    flipPermP n x = ((x.1.2, x.1.1), x.2) := rfl

@[simp] theorem flipPermP_symm_apply (n : ℕ) (x : (Fin n × Fin n) × Fin n) :
    (flipPermP n).symm x = ((x.1.2, x.1.1), x.2) := rfl

@[simp] theorem cycPermP_apply (n : ℕ) (x : (Fin n × Fin n) × Fin n) :
    cycPermP n x = ((x.2, x.1.1), x.1.2) := rfl

@[simp] theorem cycPermP_symm_apply (n : ℕ) (x : (Fin n × Fin n) × Fin n) :
    (cycPermP n).symm x = ((x.1.2, x.2), x.1.1) := rfl

theorem cycPermP_cube (n : ℕ) : cycPermP n * cycPermP n * cycPermP n = 1 := by
  apply Equiv.ext
  intro x
  rcases x with ⟨⟨i, j⟩, k⟩
  simp [Equiv.Perm.mul_apply, cycPermP]

theorem flipPermP_self (n : ℕ) : flipPermP n * flipPermP n = 1 := by
  apply Equiv.ext
  intro x
  rcases x with ⟨⟨i, j⟩, k⟩
  simp [Equiv.Perm.mul_apply, flipPermP]

/-- Conjugating the cyclic permutation by the flip inverts it. -/
theorem flipPermP_conj_cycPermP (n : ℕ) :
    (flipPermP n).symm.trans ((cycPermP n).trans (flipPermP n)) =
      (cycPermP n).trans (cycPermP n) := by
  apply Equiv.ext
  intro x
  rcases x with ⟨⟨i, j⟩, k⟩
  simp [Equiv.trans_apply, flipPermP, cycPermP]

/-! ## The triple Kronecker product -/

section Kron

variable [Ring A]

/-- `G ⊗ G ⊗ G` on the index type `(Fin n × Fin n) × Fin n`. -/
def kron3 {n : ℕ} (G : Matrix (Fin n) (Fin n) A) :
    Matrix ((Fin n × Fin n) × Fin n) ((Fin n × Fin n) × Fin n) A :=
  kroneckerMap (· * ·) (kroneckerMap (· * ·) G G) G

@[simp] theorem kron3_apply {n : ℕ} (G : Matrix (Fin n) (Fin n) A)
    (x y : (Fin n × Fin n) × Fin n) :
    kron3 G x y = (G x.1.1 y.1.1 * G x.1.2 y.1.2) * G x.2 y.2 := rfl

theorem kron3_mul_self {n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (G : Matrix (Fin n) (Fin n) A) : kron3 G * kron3 G = kron3 (G * G) := by
  have hmul : kron3 G * kron3 G =
      kroneckerMap (· * ·)
        (kroneckerMap (· * ·) G G * kroneckerMap (· * ·) G G) (G * G) := by
    letI : CommSemiring A := { ‹Ring A› with mul_comm := hA }
    show kroneckerMap (· * ·) (kroneckerMap (· * ·) G G) G *
        kroneckerMap (· * ·) (kroneckerMap (· * ·) G G) G = _
    rw [Matrix.mul_kronecker_mul]
  rw [hmul]
  congr 1
  letI : CommSemiring A := { ‹Ring A› with mul_comm := hA }
  exact (Matrix.mul_kronecker_mul G G G G).symm

theorem kron3_idem {n : ℕ} (hA : ∀ x y : A, x * y = y * x) (G : Matrix (Fin n) (Fin n) A)
    (hG : G * G = G) : kron3 G * kron3 G = kron3 G := by
  rw [kron3_mul_self hA G, hG]

/-- `kron3 G` is invariant under the cyclic permutation of the three tensor factors. -/
theorem reindex_cyc_kron3 {n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (G : Matrix (Fin n) (Fin n) A) :
    Matrix.reindex (cycPermP n) (cycPermP n) (kron3 G) = kron3 G := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, kron3_apply, cycPermP_symm_apply]
  ring

/-- `kron3 G` is invariant under the flip of the first two tensor factors. -/
theorem reindex_flip_kron3 {n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (G : Matrix (Fin n) (Fin n) A) :
    Matrix.reindex (flipPermP n) (flipPermP n) (kron3 G) = kron3 G := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, kron3_apply, flipPermP_symm_apply]
  ring

end Kron

/-! ## The spectral projector of the cyclic permutation -/

section Proj

variable [Ring A] [Algebra ℂ A]

/-- The spectral projector `(1 + λ⁻¹ c + λ⁻² c²)/3` of the cyclic permutation `c` on
`(Fin n × Fin n) × Fin n`, as it appears in `cubePartP`. -/
def cubeProj (p : Mat A) (lam : ℂ) :
    Matrix ((Fin p.1 × Fin p.1) × Fin p.1) ((Fin p.1 × Fin p.1) × Fin p.1) A :=
  algebraMap ℂ A (1 / 3) •
    (1 + algebraMap ℂ A lam⁻¹ • Equiv.Perm.permMatrix A (cycPermP p.1) +
      algebraMap ℂ A (lam⁻¹ ^ 2) •
        (Equiv.Perm.permMatrix A (cycPermP p.1) *
          Equiv.Perm.permMatrix A (cycPermP p.1)))

theorem cubePartP_eq_kron3_mul (lam : ℂ) (p : Mat A) :
    cubePartP lam p = kron3 p.2 * cubeProj p lam := rfl

theorem cubeProj_eq (p : Mat A) (lam : ℂ) :
    cubeProj p lam =
      algebraMap ℂ A (1 / 3) •
        (1 + algebraMap ℂ A lam⁻¹ • Equiv.Perm.permMatrix A (cycPermP p.1) +
          algebraMap ℂ A (lam⁻¹ ^ 2) •
            (Equiv.Perm.permMatrix A (cycPermP p.1) *
              Equiv.Perm.permMatrix A (cycPermP p.1))) := rfl

end Proj

end

end Work.KT.Psi

namespace Work.KT.Psi

open Matrix

noncomputable section

/-! ## The permutation matrix of the cyclic permutation is of order three -/

section PermMat

variable {A : Type} [Ring A]

theorem permMatrix_cycPermP_cube {n : ℕ} :
    Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n) *
      Equiv.Perm.permMatrix A (cycPermP n) = 1 := by
  have hc : cycPermP n * (cycPermP n * cycPermP n) = 1 := by
    rw [← mul_assoc]; exact cycPermP_cube n
  have h : (cycPermP n * (cycPermP n * cycPermP n)).permMatrix A =
      (Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n)) *
        Equiv.Perm.permMatrix A (cycPermP n) := by
    rw [Matrix.permMatrix_mul, Matrix.permMatrix_mul]
  rw [hc, Matrix.permMatrix_one] at h
  exact h.symm

theorem permMatrix_cycPermP_pow_four {n : ℕ} :
    Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n) *
      Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n) =
        Equiv.Perm.permMatrix A (cycPermP n) := by
  rw [show Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n) *
      Equiv.Perm.permMatrix A (cycPermP n) = 1 from permMatrix_cycPermP_cube, one_mul]

/-- `kron3 G` commutes with the permutation matrix of the cyclic permutation. -/
theorem kron3_mul_permMatrix_cyc {n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (G : Matrix (Fin n) (Fin n) A) :
    kron3 G * Equiv.Perm.permMatrix A (cycPermP n) =
      Equiv.Perm.permMatrix A (cycPermP n) * kron3 G := by
  have hK : (kron3 G).submatrix (cycPermP n).symm (cycPermP n).symm = kron3 G := by
    rw [← Matrix.reindex_apply]
    exact reindex_cyc_kron3 hA G
  have h1 : kron3 G * Equiv.Perm.permMatrix A (cycPermP n) =
      (kron3 G).submatrix id (cycPermP n).symm := by
    simpa [Equiv.Perm.permMatrix] using
      PEquiv.mul_toMatrix_toPEquiv (kron3 G) (cycPermP n)
  have h2 : Equiv.Perm.permMatrix A (cycPermP n) * kron3 G =
      (kron3 G).submatrix (cycPermP n) id := by
    simpa [Equiv.Perm.permMatrix] using
      PEquiv.toMatrix_toPEquiv_mul (cycPermP n) (kron3 G)
  rw [h1, h2]
  have key : (kron3 G).submatrix (cycPermP n) id =
      (kron3 G).submatrix id (cycPermP n).symm := by
    conv_lhs => rw [← hK]
    rw [Matrix.submatrix_submatrix]
    simp
  exact key.symm

end PermMat

/-! ## Scalar identities for the primitive cube root of unity -/

theorem omega_sq_inv : (omega ^ 2)⁻¹ = omega := by
  rw [← inv_pow, omega_inv_sq]

theorem omega_sq_inv_sq : (((omega ^ 2))⁻¹) ^ 2 = omega ^ 2 := by
  rw [omega_sq_inv]

theorem omega_inv_pow_three : (omega⁻¹) ^ 3 = 1 := by
  rw [inv_pow, omega_pow_three, inv_one]

theorem omega_sq_pow_three : (omega ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, omega_pow_three, one_pow]

end

end Work.KT.Psi

namespace Work.KT.Psi

open Matrix

noncomputable section

/-! ## The spectral projector, with complex scalars

`cubeProjC n lam` is the matrix of the projector `(1 + λ⁻¹c + λ⁻²c²)/3` written with scalars in
`ℂ` (rather than the equivalent `algebraMap ℂ A` scalars of `cubeProj`).  The two forms are equal
(`cubeProj_eq_cubeProjC`), and the complex-scalar form is the convenient one for the module
identities. -/

section ProjC

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The spectral projector `(1 + λ⁻¹ c + λ⁻² c²)/3` of the cyclic permutation `c`, with scalars
in `ℂ`. -/
def cubeProjC (n : ℕ) (lam : ℂ) :
    Matrix ((Fin n × Fin n) × Fin n) ((Fin n × Fin n) × Fin n) A :=
  (1 / 3 : ℂ) •
    (1 + (lam⁻¹ : ℂ) • Equiv.Perm.permMatrix A (cycPermP n) +
      ((lam⁻¹) ^ 2 : ℂ) •
        (Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n)))

theorem cubeProjC_eq (n : ℕ) (lam : ℂ) :
    cubeProjC (A := A) n lam =
      (1 / 3 : ℂ) •
        (1 + (lam⁻¹ : ℂ) • Equiv.Perm.permMatrix A (cycPermP n) +
          ((lam⁻¹) ^ 2 : ℂ) •
            (Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n))) := rfl

/-- An `A`-scalar `algebraMap ℂ A c` acts on matrices exactly as the complex scalar `c`. -/
theorem algebraMap_smul_eq_smul_C {ι : Type} (c : ℂ) (M : Matrix ι ι A) :
    (algebraMap ℂ A c) • M = c • M := by
  ext i j
  simp only [Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]

/-- `reindex` commutes with complex scalars. -/
theorem reindex_smul_C {ι κ : Type} (e : ι ≃ κ) (c : ℂ) (X : Matrix ι ι A) :
    Matrix.reindex e e (c • X) = c • Matrix.reindex e e X := rfl

theorem cubeProj_eq_cubeProjC (p : Mat A) (lam : ℂ) :
    cubeProj p lam = cubeProjC (A := A) p.1 lam := by
  simp only [cubeProj, cubeProjC, algebraMap_smul_eq_smul_C]

theorem reindex_flip_permMatrix_cyc (n : ℕ) :
    Matrix.reindex (flipPermP n) (flipPermP n) (Equiv.Perm.permMatrix A (cycPermP n)) =
      Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n) := by
  rw [reindex_permMatrix, flipPermP_conj_cycPermP]
  rw [show (cycPermP n).trans (cycPermP n) = cycPermP n * cycPermP n from by
    rw [Equiv.Perm.mul_def], Matrix.permMatrix_mul]

theorem reindex_flip_permMatrix_cyc_sq (n : ℕ) :
    Matrix.reindex (flipPermP n) (flipPermP n)
      (Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n)) =
      Equiv.Perm.permMatrix A (cycPermP n) := by
  rw [reindex_mul', reindex_flip_permMatrix_cyc, ← mul_assoc,
    show Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n) *
      Equiv.Perm.permMatrix A (cycPermP n) = 1 from permMatrix_cycPermP_cube, one_mul]

end ProjC

end

end Work.KT.Psi

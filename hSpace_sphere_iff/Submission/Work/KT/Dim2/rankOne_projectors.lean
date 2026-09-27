import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.kronMat_swap_comm

/-!
# Projectors on a rank-one `2 × 2` idempotent

Let `p` be a `2 × 2` matrix over a `ℂ`-algebra `A` whose entries satisfy the rank-one
relation `p i l * p j k = p i k * p j l` (the identity satisfied by the entries of a rank-one
matrix `p i j = a i · b j`).  Then the Kronecker square `p ⊗ p` is fixed by the swap of the
two tensor factors and the Kronecker cube `p ⊗ p ⊗ p` is fixed by the cyclic permutation of
the three factors.  Consequently

* `sq2Part 1 p = p ⊗ p` (the symmetric part is everything),
* `sq2Part (-1) p = 0` (the alternating part vanishes),
* `cubePart 1 p = p ⊗ p ⊗ p`,
* `cubePart ω p = 0` (the spectral projector at the primitive cube root of unity kills it).

The proof is an entrywise computation, transported along the reindexings that relate the
product index types `Fin n × Fin n` and `(Fin n × Fin n) × Fin n` to `Fin (n * n)` and
`Fin (n * n * n)`.
-/

namespace Work.KT.Dim2

open Matrix

noncomputable section

/-! ## Generalities -/

variable {A : Type} [Ring A]

/-- A scoped version of the identity `algebraMap ℂ A c • M = c • M` for square matrices. -/
lemma algebraMap_smul_eq_smul_C' [Algebra ℂ A] {ι : Type} (c : ℂ) (M : Matrix ι ι A) :
    algebraMap ℂ A c • M = c • M := by
  ext i j
  simp only [Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]

/-- The rank-one relation lets one cyclically rotate the last three indices of a triple product. -/
lemma rankOne_rot (p : Matrix (Fin 2) (Fin 2) A)
    (h1 : ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l)
    (a1 a2 a3 b1 b2 b3 : Fin 2) :
    (p a1 b1 * p a2 b2) * p a3 b3 = (p a1 b3 * p a2 b1) * p a3 b2 := by
  rw [h1 a1 a2 b1 b3, mul_assoc, h1 a2 a3 b3 b2, mul_assoc]

/-- On the product index type, `p ⊗ p` is fixed by the swap of the two factors. -/
lemma kroneckerMap_self_mul_prodComm (p : Matrix (Fin 2) (Fin 2) A)
    (h1 : ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l) :
    Matrix.kroneckerMap (· * ·) p p * Equiv.Perm.permMatrix A (Equiv.prodComm (Fin 2) (Fin 2))
      = Matrix.kroneckerMap (· * ·) p p := by
  rw [Work.KT.Psi.mul_permMatrix_submatrix, Equiv.prodComm_symm]
  ext i j
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  simp only [Matrix.submatrix_apply, id_eq, Equiv.prodComm_apply, Prod.swap_prod_mk]
  exact h1 i1 i2 j1 j2

/-- On the reindexed side, `p ⊗ p` is fixed by `swapPerm 2`. -/
lemma kronMat_self_mul_swap (p : Matrix (Fin 2) (Fin 2) A)
    (h1 : ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l) :
    Work.KT.kronMat p p * Equiv.Perm.permMatrix A (Work.KT.swapPerm 2) = Work.KT.kronMat p p := by
  let e : Fin 2 × Fin 2 ≃ Fin (2 * 2) := finProdFinEquiv
  let K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A := Matrix.kroneckerMap (· * ·) p p
  let S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
    Equiv.Perm.permMatrix A (Equiv.prodComm (Fin 2) (Fin 2))
  have hK : Work.KT.kronMat p p = Matrix.reindex e e K := rfl
  have hswap : e.symm.trans ((Equiv.prodComm (Fin 2) (Fin 2)).trans e) = Work.KT.swapPerm 2 := by
    rw [← Equiv.trans_assoc]; rfl
  have hS : Equiv.Perm.permMatrix A (Work.KT.swapPerm 2) = Matrix.reindex e e S := by
    rw [← hswap, ← Work.KT.reindex_permMatrix e (Equiv.prodComm (Fin 2) (Fin 2))]
  have hKS : K * S = K := kroneckerMap_self_mul_prodComm p h1
  calc Work.KT.kronMat p p * Equiv.Perm.permMatrix A (Work.KT.swapPerm 2)
      = Matrix.reindex e e K * Matrix.reindex e e S := by rw [hK, hS]
    _ = Matrix.reindex e e (K * S) := (map_mul (Matrix.reindexRingEquiv A e) K S).symm
    _ = Matrix.reindex e e K := by rw [hKS]
    _ = Work.KT.kronMat p p := hK.symm

/-- The inverse of the cyclic permutation `cycPermP 2` on `(Fin 2 × Fin 2) × Fin 2`. -/
@[simp] lemma cycPermP_two_symm_apply (x : (Fin 2 × Fin 2) × Fin 2) :
    (Work.KT.cycPermP 2).symm x = ((x.1.2, x.2), x.1.1) := rfl

/-- On the product index type, `p ⊗ p ⊗ p` is fixed by the cyclic permutation. -/
lemma kron3Map_mul_cycPermP (p : Matrix (Fin 2) (Fin 2) A)
    (h1 : ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l) :
    Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p *
        Equiv.Perm.permMatrix A (Work.KT.cycPermP 2)
      = Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p := by
  rw [Work.KT.Psi.mul_permMatrix_submatrix]
  ext x y
  rcases x with ⟨⟨i1, i2⟩, i3⟩
  rcases y with ⟨⟨k1, k2⟩, k3⟩
  simp only [Matrix.submatrix_apply, id_eq, cycPermP_two_symm_apply]
  exact rankOne_rot p h1 i1 i2 i3 k2 k3 k1

/-- On the product index type, `p ⊗ p ⊗ p` is fixed by the square of the cyclic permutation. -/
lemma kron3Map_mul_cycPermP_sq (p : Matrix (Fin 2) (Fin 2) A)
    (h1 : ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l) :
    Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p *
        (Equiv.Perm.permMatrix A (Work.KT.cycPermP 2) *
          Equiv.Perm.permMatrix A (Work.KT.cycPermP 2))
      = Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p := by
  rw [← mul_assoc, kron3Map_mul_cycPermP p h1, kron3Map_mul_cycPermP p h1]

/-- On the reindexed side, `p ⊗ p ⊗ p` is fixed by `cycPerm 2`. -/
lemma kronMat_kronMat_mul_cyc (p : Matrix (Fin 2) (Fin 2) A) [Algebra ℂ A]
    (h1 : ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l) :
    Work.KT.kronMat (Work.KT.kronMat p p) p * Equiv.Perm.permMatrix A (Work.KT.cycPerm 2)
      = Work.KT.kronMat (Work.KT.kronMat p p) p := by
  have hQ : Work.KT.kronMat (Work.KT.kronMat p p) p
      = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
          (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p) :=
    (Work.KT.kronMat_kronMat_eq (⟨2, p⟩ : Work.KT.Mat A)).symm
  have hD : Equiv.Perm.permMatrix A (Work.KT.cycPerm 2)
      = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
          (Equiv.Perm.permMatrix A (Work.KT.cycPermP 2)) :=
    (Work.KT.reindex_permMatrix_cyc 2).symm
  calc Work.KT.kronMat (Work.KT.kronMat p p) p * Equiv.Perm.permMatrix A (Work.KT.cycPerm 2)
      = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
            (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p) *
          Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
            (Equiv.Perm.permMatrix A (Work.KT.cycPermP 2)) := by rw [hQ, hD]
    _ = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
            (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p *
              Equiv.Perm.permMatrix A (Work.KT.cycPermP 2)) :=
        (map_mul (Matrix.reindexRingEquiv A (Work.KT.cycIdx 2).symm) _ _).symm
    _ = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
            (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p) := by
        rw [kron3Map_mul_cycPermP p h1]
    _ = Work.KT.kronMat (Work.KT.kronMat p p) p := hQ.symm

/-- On the reindexed side, `p ⊗ p ⊗ p` is fixed by the square of `cycPerm 2`. -/
lemma kronMat_kronMat_mul_cyc_sq (p : Matrix (Fin 2) (Fin 2) A) [Algebra ℂ A]
    (h1 : ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l) :
    Work.KT.kronMat (Work.KT.kronMat p p) p *
        (Equiv.Perm.permMatrix A (Work.KT.cycPerm 2) *
          Equiv.Perm.permMatrix A (Work.KT.cycPerm 2))
      = Work.KT.kronMat (Work.KT.kronMat p p) p := by
  have hQ : Work.KT.kronMat (Work.KT.kronMat p p) p
      = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
          (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p) :=
    (Work.KT.kronMat_kronMat_eq (⟨2, p⟩ : Work.KT.Mat A)).symm
  have hD : Equiv.Perm.permMatrix A (Work.KT.cycPerm 2)
      = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
          (Equiv.Perm.permMatrix A (Work.KT.cycPermP 2)) :=
    (Work.KT.reindex_permMatrix_cyc 2).symm
  have hD2 : Equiv.Perm.permMatrix A (Work.KT.cycPerm 2) *
        Equiv.Perm.permMatrix A (Work.KT.cycPerm 2)
      = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
          (Equiv.Perm.permMatrix A (Work.KT.cycPermP 2) *
            Equiv.Perm.permMatrix A (Work.KT.cycPermP 2)) := by
    rw [hD, ← Work.KT.reindex_mul' (Work.KT.cycIdx 2).symm
      (Equiv.Perm.permMatrix A (Work.KT.cycPermP 2))
      (Equiv.Perm.permMatrix A (Work.KT.cycPermP 2))]
  calc Work.KT.kronMat (Work.KT.kronMat p p) p *
        (Equiv.Perm.permMatrix A (Work.KT.cycPerm 2) *
          Equiv.Perm.permMatrix A (Work.KT.cycPerm 2))
      = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
            (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p) *
          Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
            (Equiv.Perm.permMatrix A (Work.KT.cycPermP 2) *
              Equiv.Perm.permMatrix A (Work.KT.cycPermP 2)) := by rw [hQ, hD2]
    _ = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
            (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p *
              (Equiv.Perm.permMatrix A (Work.KT.cycPermP 2) *
                Equiv.Perm.permMatrix A (Work.KT.cycPermP 2))) :=
        (map_mul (Matrix.reindexRingEquiv A (Work.KT.cycIdx 2).symm) _ _).symm
    _ = Matrix.reindex (Work.KT.cycIdx 2).symm (Work.KT.cycIdx 2).symm
            (Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) p p) p) := by
        rw [kron3Map_mul_cycPermP_sq p h1]
    _ = Work.KT.kronMat (Work.KT.kronMat p p) p := hQ.symm

/-! ## The complex scalars in the definitions of `sq2Part` and `cubePart` -/

section Scalars

variable [Algebra ℂ A]

/-- `sq2Part 1 p` with the scalar `1/2` read in `ℂ`. -/
lemma sq2Part_one_eq' (p : Work.KT.Mat A) :
    Work.KT.sq2Part (1 : ℂ) p = ⟨p.1 * p.1, Work.KT.kronMat p.2 p.2 *
      ((1 / 2 : ℂ) • (1 + Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)))⟩ := by
  show (⟨p.1 * p.1, Work.KT.kronMat p.2 p.2 *
      (algebraMap ℂ A (1 / 2) • (1 + algebraMap ℂ A (1 : ℂ) •
        Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)))⟩ : Work.KT.Mat A) = _
  rw [show algebraMap ℂ A (1 : ℂ) • Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)
        = (1 : ℂ) • Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1) from by
        ext i j; simp [Matrix.smul_apply, Algebra.smul_def],
      one_smul,
      show algebraMap ℂ A (1 / 2 : ℂ) •
          (1 + Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)) = (1 / 2 : ℂ) •
          (1 + Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)) from by
        ext i j; simp [Matrix.smul_apply, Algebra.smul_def]]

/-- `sq2Part (-1) p` with the scalar `1/2` read in `ℂ`. -/
lemma sq2Part_neg_one_eq' (p : Work.KT.Mat A) :
    Work.KT.sq2Part (-1 : ℂ) p = ⟨p.1 * p.1, Work.KT.kronMat p.2 p.2 *
      ((1 / 2 : ℂ) • (1 - Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)))⟩ := by
  show (⟨p.1 * p.1, Work.KT.kronMat p.2 p.2 *
      (algebraMap ℂ A (1 / 2) • (1 + algebraMap ℂ A (-1 : ℂ) •
        Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)))⟩ : Work.KT.Mat A) = _
  rw [show algebraMap ℂ A (1 / 2 : ℂ) •
        (1 + algebraMap ℂ A (-1 : ℂ) • Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)) =
        (1 / 2 : ℂ) • (1 + algebraMap ℂ A (-1 : ℂ) •
          Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)) from by
        ext i j; simp [Matrix.smul_apply, Algebra.smul_def],
      show algebraMap ℂ A (-1 : ℂ) • Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1)
        = (-1 : ℂ) • Equiv.Perm.permMatrix A (Work.KT.swapPerm p.1) from by
        ext i j; simp [Matrix.smul_apply, Algebra.smul_def],
      neg_one_smul, sub_eq_add_neg]

/-- `cubePart 1 p` with both scalars read in `ℂ` (the eigenvalue is `1`). -/
lemma cubePart_one_eq' (p : Work.KT.Mat A) :
    Work.KT.cubePart (1 : ℂ) p = ⟨p.1 * p.1 * p.1,
      Work.KT.kronMat (Work.KT.kronMat p.2 p.2) p.2 *
        ((1 / 3 : ℂ) • (1 + Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) +
          (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
            Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1))))⟩ := by
  show (⟨p.1 * p.1 * p.1, Work.KT.kronMat (Work.KT.kronMat p.2 p.2) p.2 *
      (algebraMap ℂ A (1 / 3) • (1 + algebraMap ℂ A ((1 : ℂ)⁻¹) •
          Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) +
        algebraMap ℂ A (((1 : ℂ)⁻¹) ^ 2) •
          (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
            Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1))))⟩ : Work.KT.Mat A) = _
  rw [inv_one, one_pow,
    show algebraMap ℂ A (1 : ℂ) • Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1)
      = (1 : ℂ) • Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) from by
      ext i j; simp [Matrix.smul_apply, Algebra.smul_def],
    one_smul,
    show algebraMap ℂ A (1 : ℂ) • (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
        Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1))
      = (1 : ℂ) • (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
        Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1)) from by
      ext i j; simp [Matrix.smul_apply, Algebra.smul_def],
    one_smul,
    show algebraMap ℂ A (1 / 3 : ℂ) •
        (1 + Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) +
          Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
            Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1)) =
        (1 / 3 : ℂ) • (1 + Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) +
          Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
            Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1)) from by
      ext i j; simp [Matrix.smul_apply, Algebra.smul_def]]

/-- `cubePart ω p` with both scalars read in `ℂ` (the eigenvalue is `ω`). -/
lemma cubePart_omega_eq' (p : Work.KT.Mat A) :
    Work.KT.cubePart Work.KT.omega p = ⟨p.1 * p.1 * p.1,
      Work.KT.kronMat (Work.KT.kronMat p.2 p.2) p.2 *
        ((1 / 3 : ℂ) • (1 + (Work.KT.omega⁻¹) • Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) +
          ((Work.KT.omega⁻¹) ^ 2) • (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
            Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1))))⟩ := by
  show (⟨p.1 * p.1 * p.1, Work.KT.kronMat (Work.KT.kronMat p.2 p.2) p.2 *
      (algebraMap ℂ A (1 / 3) • (1 + algebraMap ℂ A (Work.KT.omega⁻¹) •
          Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) +
        algebraMap ℂ A ((Work.KT.omega⁻¹) ^ 2) •
          (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
            Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1))))⟩ : Work.KT.Mat A) = _
  rw [show algebraMap ℂ A (Work.KT.omega⁻¹) • Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1)
        = (Work.KT.omega⁻¹) • Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) from by
        ext i j; simp [Matrix.smul_apply, Algebra.smul_def],
      show algebraMap ℂ A ((Work.KT.omega⁻¹) ^ 2) •
          (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
            Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1))
        = ((Work.KT.omega⁻¹) ^ 2) • (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
            Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1)) from by
        ext i j; simp [Matrix.smul_apply, Algebra.smul_def],
      show algebraMap ℂ A (1 / 3 : ℂ) •
          (1 + (Work.KT.omega⁻¹) • Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) +
            ((Work.KT.omega⁻¹) ^ 2) • (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
              Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1))) =
          (1 / 3 : ℂ) • (1 + (Work.KT.omega⁻¹) • Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) +
            ((Work.KT.omega⁻¹) ^ 2) • (Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1) *
              Equiv.Perm.permMatrix A (Work.KT.cycPerm p.1))) from by
        ext i j; simp [Matrix.smul_apply, Algebra.smul_def]]

end Scalars

/-! ## The cube root of unity -/

/-- `ω ≠ 1`. -/
lemma omega_ne_one : Work.KT.omega ≠ 1 := by
  have h := Complex.isPrimitiveRoot_exp_of_coprime 1 3 (by norm_num) (by norm_num)
  have h' : Work.KT.omega = Complex.exp (2 * ↑Real.pi * Complex.I * ((1 : ℕ) / 3 : ℂ)) := by
    rw [Work.KT.omega]; congr 1; push_cast; ring
  rw [h']
  exact h.ne_one (by norm_num)

/-- `1 + ω⁻¹ + (ω⁻¹)² = 0`. -/
lemma omega_inv_sum : (1 : ℂ) + Work.KT.omega⁻¹ + Work.KT.omega⁻¹ ^ 2 = 0 := by
  have h1 : Work.KT.omega ^ 2 + Work.KT.omega + 1 = 0 := by
    have h2 : (Work.KT.omega - 1) * (Work.KT.omega ^ 2 + Work.KT.omega + 1) = 0 := by
      have h3 : (Work.KT.omega - 1) * (Work.KT.omega ^ 2 + Work.KT.omega + 1) =
          Work.KT.omega ^ 3 - 1 := by ring
      rw [h3, Work.KT.omega_pow_three]; ring
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (sub_ne_zero.mpr omega_ne_one)
    · exact h
  rw [Work.KT.omega_inv_sq, Work.KT.omega_inv,
    show (1 : ℂ) + Work.KT.omega ^ 2 + Work.KT.omega =
      Work.KT.omega ^ 2 + Work.KT.omega + 1 by ring, h1]

/-! ## The main statement -/

end

noncomputable section

theorem rankOne_projectors {A : Type} [Ring A] [Algebra ℂ A] (p : Matrix (Fin 2) (Fin 2) A)
    (h1 : ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l) :
    Work.KT.sq2Part (1 : ℂ) (⟨2, p⟩ : Work.KT.Mat A) =
        Work.KT.Mat.kron (⟨2, p⟩ : Work.KT.Mat A) (⟨2, p⟩ : Work.KT.Mat A) ∧
      Work.KT.sq2Part (-1 : ℂ) (⟨2, p⟩ : Work.KT.Mat A) =
        (⟨2 * 2, (0 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) A)⟩ : Work.KT.Mat A) ∧
      Work.KT.cubePart (1 : ℂ) (⟨2, p⟩ : Work.KT.Mat A) =
        Work.KT.Mat.kron (Work.KT.Mat.kron (⟨2, p⟩ : Work.KT.Mat A) (⟨2, p⟩ : Work.KT.Mat A))
          (⟨2, p⟩ : Work.KT.Mat A) ∧
      Work.KT.cubePart Work.KT.omega (⟨2, p⟩ : Work.KT.Mat A) =
        (⟨2 * 2 * 2, (0 : Matrix (Fin (2 * 2 * 2)) (Fin (2 * 2 * 2)) A)⟩ : Work.KT.Mat A)
    := by
  have hDS : Work.KT.kronMat p p * Equiv.Perm.permMatrix A (Work.KT.swapPerm 2)
      = Work.KT.kronMat p p := kronMat_self_mul_swap p h1
  have hDC : Work.KT.kronMat (Work.KT.kronMat p p) p * Equiv.Perm.permMatrix A (Work.KT.cycPerm 2)
      = Work.KT.kronMat (Work.KT.kronMat p p) p := kronMat_kronMat_mul_cyc p h1
  have hDC2 : Work.KT.kronMat (Work.KT.kronMat p p) p *
      (Equiv.Perm.permMatrix A (Work.KT.cycPerm 2) * Equiv.Perm.permMatrix A (Work.KT.cycPerm 2))
      = Work.KT.kronMat (Work.KT.kronMat p p) p := kronMat_kronMat_mul_cyc_sq p h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sq2Part_one_eq']
    rw [show Work.KT.kronMat p p * ((1 / 2 : ℂ) •
          (1 + Equiv.Perm.permMatrix A (Work.KT.swapPerm 2))) = Work.KT.kronMat p p from by
      rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, hDS, smul_add, ← add_smul]
      norm_num]
    rfl
  · rw [sq2Part_neg_one_eq']
    rw [show Work.KT.kronMat p p * ((1 / 2 : ℂ) •
          (1 - Equiv.Perm.permMatrix A (Work.KT.swapPerm 2))) = 0 from by
      rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hDS, sub_self, smul_zero]]
  · rw [cubePart_one_eq']
    rw [show Work.KT.kronMat (Work.KT.kronMat p p) p * ((1 / 3 : ℂ) •
          (1 + Equiv.Perm.permMatrix A (Work.KT.cycPerm 2) +
            Equiv.Perm.permMatrix A (Work.KT.cycPerm 2) *
              Equiv.Perm.permMatrix A (Work.KT.cycPerm 2))) =
          Work.KT.kronMat (Work.KT.kronMat p p) p from by
      rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, hDC, hDC2]
      have hcoef : Work.KT.kronMat (Work.KT.kronMat p p) p +
            Work.KT.kronMat (Work.KT.kronMat p p) p +
            Work.KT.kronMat (Work.KT.kronMat p p) p =
          (3 : ℂ) • Work.KT.kronMat (Work.KT.kronMat p p) p := by
        rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
      rw [hcoef, smul_smul, show (1 / 3 : ℂ) * 3 = 1 by norm_num, one_smul]]
    rfl
  · rw [cubePart_omega_eq']
    rw [show Work.KT.kronMat (Work.KT.kronMat p p) p * ((1 / 3 : ℂ) •
          (1 + (Work.KT.omega⁻¹) • Equiv.Perm.permMatrix A (Work.KT.cycPerm 2) +
            (Work.KT.omega⁻¹ ^ 2) • (Equiv.Perm.permMatrix A (Work.KT.cycPerm 2) *
              Equiv.Perm.permMatrix A (Work.KT.cycPerm 2)))) = 0 from by
      rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one,
        Matrix.mul_smul, Matrix.mul_smul, hDC, hDC2]
      have hcoef : Work.KT.kronMat (Work.KT.kronMat p p) p +
            (Work.KT.omega⁻¹) • Work.KT.kronMat (Work.KT.kronMat p p) p +
            (Work.KT.omega⁻¹ ^ 2) • Work.KT.kronMat (Work.KT.kronMat p p) p =
          ((1 : ℂ) + Work.KT.omega⁻¹ + Work.KT.omega⁻¹ ^ 2) •
            Work.KT.kronMat (Work.KT.kronMat p p) p := by
        rw [add_smul, add_smul, one_smul]
      rw [hcoef, omega_inv_sum, zero_smul, smul_zero]]

end

end Work.KT.Dim2

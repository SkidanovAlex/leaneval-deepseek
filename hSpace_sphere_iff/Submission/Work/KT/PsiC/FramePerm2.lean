import Mathlib
import Submission.Work.KT.PsiC.Setup
import Submission.Work.KT.PsiC.ReindexAux
import Submission.Work.KT.PsiC.CycProj
import Submission.Work.KT.PsiC.FramePerm
import Submission.Work.KT.Psi.k3Aux

namespace Work.KT.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]
variable {α : Type} [Fintype α] [DecidableEq α]

theorem mul_permMatrix (M : Matrix α α A) (σ : Equiv.Perm α) (a b : α) :
    (M * σ.permMatrix A) a b = M a (σ.symm b) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ.symm b)]
  · rw [permMatrix_apply', if_pos (σ.apply_symm_apply b), mul_one]
  · intro c _ hc
    rw [permMatrix_apply', if_neg (fun h => hc (by rw [← h]; exact (Equiv.symm_apply_apply σ c).symm)),
      mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem permMatrix_mul (σ : Equiv.Perm α) (M : Matrix α α A) (a b : α) :
    (σ.permMatrix A * M) a b = M (σ a) b := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ a)]
  · rw [permMatrix_apply', if_pos rfl, one_mul]
  · intro c _ hc
    rw [permMatrix_apply', if_neg (fun h => hc h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem cycPermP_apply' (n : ℕ) (x : I3 n) :
    cycPermP n x = ((x.2, x.1.1), x.1.2) := rfl

@[simp] theorem cycPermP_symm_apply' (n : ℕ) (x : I3 n) :
    (cycPermP n).symm x = ((x.1.2, x.2), x.1.1) := rfl

@[simp] theorem flipI3_apply' (n : ℕ) (x : I3 n) : flipI3 n x = ((x.1.2, x.1.1), x.2) := rfl

@[simp] theorem flipI3_symm_apply' (n : ℕ) (x : I3 n) :
    (flipI3 n).symm x = ((x.1.2, x.1.1), x.2) := rfl

@[simp] theorem prodComm_apply' (x : α × α) : Equiv.prodComm α α x = (x.2, x.1) := rfl

@[simp] theorem prodComm_symm_apply' (x : α × α) :
    (Equiv.prodComm α α).symm x = (x.2, x.1) := rfl

theorem kron_prodComm (M N : Matrix α α A) (hA : ∀ x y : A, x * y = y * x) :
    kroneckerMap (· * ·) M N * Equiv.Perm.permMatrix A (Equiv.prodComm α α) =
      Equiv.Perm.permMatrix A (Equiv.prodComm α α) * kroneckerMap (· * ·) N M := by
  ext x y
  rw [mul_permMatrix, permMatrix_mul, Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
  exact hA _ _

theorem K3_apply (p : Mat A) (x y : I3 p.1) :
    kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2 x y =
      (p.2 x.1.1 y.1.1 * p.2 x.1.2 y.1.2) * p.2 x.2 y.2 := rfl

theorem K2_apply (p : Mat A) (x y : I2 p.1) :
    kroneckerMap (· * ·) p.2 p.2 x y = p.2 x.1 y.1 * p.2 x.2 y.2 := rfl

theorem K3_comm_cycPermP (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2 * (cycPermP p.1).permMatrix A =
      (cycPermP p.1).permMatrix A *
        kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2 := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext x y
  rw [mul_permMatrix, permMatrix_mul, K3_apply, K3_apply]
  simp only [cycPermP_symm_apply', cycPermP_apply']
  ring

theorem K3_comm_flipI3 (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2 * (flipI3 p.1).permMatrix A =
      (flipI3 p.1).permMatrix A *
        kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2 := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext x y
  rw [mul_permMatrix, permMatrix_mul, K3_apply, K3_apply]
  simp only [flipI3_symm_apply', flipI3_apply']
  ring

end

end Work.KT.PsiC

namespace Work.KT.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]
variable {α : Type} [Fintype α] [DecidableEq α]
variable {β : Type} [Fintype β] [DecidableEq β]

theorem kron_mul'' (hA : ∀ x y : A, x * y = y * x) (M N : Matrix α α A) (P Q : Matrix β β A) :
    kroneckerMap (· * ·) M P * kroneckerMap (· * ·) N Q =
      kroneckerMap (· * ·) (M * N) (P * Q) := by
  letI : CommSemiring A := { ‹Ring A› with mul_comm := hA }
  exact (Matrix.mul_kronecker_mul M N P Q).symm

theorem kroneckerMap_permMatrix' (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    kroneckerMap (· * ·) (Equiv.Perm.permMatrix A σ) (Equiv.Perm.permMatrix A τ) =
      Equiv.Perm.permMatrix A (Equiv.prodCongr σ τ) := by
  ext x y
  rw [Matrix.kroneckerMap_apply, permMatrix_apply', permMatrix_apply', permMatrix_apply']
  by_cases h1 : σ x.1 = y.1 <;> by_cases h2 : τ x.2 = y.2 <;>
    simp [h1, h2, Prod.ext_iff]

theorem PA_idem (p : Mat A) (hA : ∀ x y : A, x * y = y * x) (hp : p.IsIdem) :
    PA p * PA p = PA p := by
  have h3 : kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2 *
      kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2 =
      kroneckerMap (· * ·) (kroneckerMap (· * ·) p.2 p.2) p.2 := by
    rw [kron_mul'' (α := I2 p.1) (β := Fin p.1) hA,
      kron_mul'' (α := Fin p.1) (β := Fin p.1) hA, hp]
  unfold PA
  rw [kron_mul'' (α := I3 p.1) (β := I3 p.1) hA, h3]

theorem PB_idem (p : Mat A) (hA : ∀ x y : A, x * y = y * x) (hp : p.IsIdem) :
    PB p * PB p = PB p := by
  have h2 : kroneckerMap (· * ·) p.2 p.2 * kroneckerMap (· * ·) p.2 p.2 =
      kroneckerMap (· * ·) p.2 p.2 := by
    rw [kron_mul'' (α := Fin p.1) (β := Fin p.1) hA, hp]
  unfold PB
  rw [kron_mul'' (α := I2 p.1 × I2 p.1) (β := I2 p.1) hA,
    kron_mul'' (α := I2 p.1) (β := I2 p.1) hA, h2]

theorem reindex_Phi_PA (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    Matrix.reindex (Phi p.1) (Phi p.1) (PA p) = PB p := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, PA, PB, Phi_symm_apply,
    Matrix.kroneckerMap_apply]
  ring

theorem PA_comm_sA (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    PA p * Equiv.Perm.permMatrix A (sA p.1) = Equiv.Perm.permMatrix A (sA p.1) * PA p := by
  unfold PA sA
  exact kron_prodComm _ _ hA

theorem PA_comm_c1A (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    PA p * Equiv.Perm.permMatrix A (c1A p.1) = Equiv.Perm.permMatrix A (c1A p.1) * PA p := by
  have hD := K3_comm_cycPermP p hA
  unfold PA c1A
  rw [← kroneckerMap_permMatrix' (A := A) (cycPermP p.1) (Equiv.refl (I3 p.1)),
    Matrix.permMatrix_refl, kron_mul'' (α := I3 p.1) (β := I3 p.1) hA,
    kron_mul'' (α := I3 p.1) (β := I3 p.1) hA, hD, Matrix.mul_one, Matrix.one_mul]

theorem PA_comm_c2A (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    PA p * Equiv.Perm.permMatrix A (c2A p.1) = Equiv.Perm.permMatrix A (c2A p.1) * PA p := by
  have hD := K3_comm_cycPermP p hA
  unfold PA c2A
  rw [← kroneckerMap_permMatrix' (A := A) (Equiv.refl (I3 p.1)) (cycPermP p.1),
    Matrix.permMatrix_refl, kron_mul'' (α := I3 p.1) (β := I3 p.1) hA,
    kron_mul'' (α := I3 p.1) (β := I3 p.1) hA, hD, Matrix.mul_one, Matrix.one_mul]

theorem PA_comm_tA (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    PA p * Equiv.Perm.permMatrix A (tA p.1) = Equiv.Perm.permMatrix A (tA p.1) * PA p := by
  have hD := K3_comm_cycPermP p hA
  unfold PA tA
  rw [← kroneckerMap_permMatrix' (A := A) (cycPermP p.1) (cycPermP p.1),
    kron_mul'' (α := I3 p.1) (β := I3 p.1) hA,
    kron_mul'' (α := I3 p.1) (β := I3 p.1) hA, hD]

theorem PA_comm_RA (p : Mat A) (hA : ∀ x y : A, x * y = y * x) :
    PA p * Equiv.Perm.permMatrix A (RA p.1) = Equiv.Perm.permMatrix A (RA p.1) * PA p := by
  have hD := K3_comm_flipI3 p hA
  unfold PA RA
  rw [← kroneckerMap_permMatrix' (A := A) (flipI3 p.1) (flipI3 p.1),
    kron_mul'' (α := I3 p.1) (β := I3 p.1) hA,
    kron_mul'' (α := I3 p.1) (β := I3 p.1) hA, hD]

end

end Work.KT.PsiC

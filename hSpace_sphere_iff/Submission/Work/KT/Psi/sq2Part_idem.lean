import Mathlib
import Submission.Work.KT.Psi.Basic

/-!
# Idempotency of `sq2Part ε p` for `ε² = 1`

`sq2Part ε p` is `p ⊗ p` cut down by the "averaging" operator `(1 + ε·τ)/2`, where `τ` is the
matrix of the swap `(i,j) ↦ (j,i)` of the index set `Fin n × Fin n`.  The two facts that make it
idempotent are

* `τ * τ = 1` (the swap is an involution),
* `(p ⊗ p) * τ = τ * (p ⊗ p)` (the swap only exchanges the two tensor factors of `p ⊗ p`),

from which `(1 + ετ)/2` is a projection since `ε² = 1`.  The hypothesis `hA` (every two elements
of `A` commute) is what lets `p ⊗ p` be manipulated as a Kronecker product.

Everything is proved directly at the level of matrices; the only index bookkeeping is the
identification `permMatrix (swapPerm n) = reindex finProdFinEquiv (permMatrix (prodComm))`
(`Work.KT.reindex_permMatrix_prodComm`).
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A]

/-- Conjugating a square matrix by the permutation matrix of `σ` permutes its entries:
`(σ • M • σ) i j = M (σ i) (σ.symm j)`. -/
theorem s2p_permMatrix_conj_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (M : Matrix ι ι A) (i j : ι) :
    (Equiv.Perm.permMatrix A σ * M * Equiv.Perm.permMatrix A σ) i j = M (σ i) (σ.symm j) := by
  rw [Matrix.mul_assoc, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The swap `(i,j) ↦ (j,i)` of `Fin n × Fin n`, transported to `Fin (n * n)` by
`finProdFinEquiv`, is an involution. -/
theorem s2p_swapPerm_mul_self (n : ℕ) : swapPerm n * swapPerm n = 1 := by
  ext x
  simp only [Equiv.Perm.mul_apply, swapPerm, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, Equiv.prodComm_apply, Prod.swap_swap, Equiv.Perm.one_apply]

/-- The permutation matrix of the swap is an involution. -/
theorem s2p_permMatrix_swapPerm_mul_self (n : ℕ) :
    Equiv.Perm.permMatrix A (swapPerm n) * Equiv.Perm.permMatrix A (swapPerm n) = 1 := by
  rw [← Matrix.permMatrix_mul, s2p_swapPerm_mul_self, Matrix.permMatrix_one]

section Algebra

variable [Algebra ℂ A]

/-- On the unreindexed product `Fin n × Fin n`, the swap fixes `p ⊗ p`: conjugating
`kroneckerMap (·*·) p p` by the permutation matrix of `prodComm` gives it back. -/
theorem s2p_prodComm_conj_kron (hA : ∀ x y : A, x * y = y * x) (p : Mat A) :
    Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)) *
      kroneckerMap (· * ·) p.2 p.2 *
      Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)) =
      kroneckerMap (· * ·) p.2 p.2 := by
  ext i j
  rw [show ((Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1))) *
      kroneckerMap (· * ·) p.2 p.2 *
      (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)))) i j
      = kroneckerMap (· * ·) p.2 p.2 (Equiv.prodComm (Fin p.1) (Fin p.1) i)
          ((Equiv.prodComm (Fin p.1) (Fin p.1)).symm j) from
    s2p_permMatrix_conj_apply _ _ _ _]
  rw [Equiv.prodComm_symm (Fin p.1) (Fin p.1)]
  simp only [Matrix.kroneckerMap_apply, Equiv.prodComm_apply]
  exact hA _ _

/-- Reindexed form: the permutation matrix of `swapPerm n` fixes `kronMat p p` by conjugation. -/
theorem s2p_kronMat_swapPerm_conj (hA : ∀ x y : A, x * y = y * x) (p : Mat A) :
    Equiv.Perm.permMatrix A (swapPerm p.1) * kronMat p.2 p.2 *
      Equiv.Perm.permMatrix A (swapPerm p.1) = kronMat p.2 p.2 := by
  have hS : Equiv.Perm.permMatrix A (swapPerm p.1) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1))) :=
    (reindex_permMatrix_prodComm (A := A) p.1).symm
  rw [hS]
  rw [show kronMat p.2 p.2 = Matrix.reindex finProdFinEquiv finProdFinEquiv
      (kroneckerMap (· * ·) p.2 p.2) from rfl]
  rw [← reindex_mul', ← reindex_mul']
  rw [s2p_prodComm_conj_kron hA p]

/-- The swap commutes with `p ⊗ p`. -/
theorem s2p_kronMat_swapPerm_comm (hA : ∀ x y : A, x * y = y * x) (p : Mat A) :
    kronMat p.2 p.2 * Equiv.Perm.permMatrix A (swapPerm p.1) =
      Equiv.Perm.permMatrix A (swapPerm p.1) * kronMat p.2 p.2 := by
  have hS : Equiv.Perm.permMatrix A (swapPerm p.1) *
      Equiv.Perm.permMatrix A (swapPerm p.1) = 1 :=
    s2p_permMatrix_swapPerm_mul_self (A := A) p.1
  have hconj := s2p_kronMat_swapPerm_conj (A := A) hA p
  calc kronMat p.2 p.2 * Equiv.Perm.permMatrix A (swapPerm p.1)
      = (Equiv.Perm.permMatrix A (swapPerm p.1) * kronMat p.2 p.2 *
          Equiv.Perm.permMatrix A (swapPerm p.1)) * Equiv.Perm.permMatrix A (swapPerm p.1) := by
        rw [hconj]
    _ = Equiv.Perm.permMatrix A (swapPerm p.1) * kronMat p.2 p.2 *
          (Equiv.Perm.permMatrix A (swapPerm p.1) * Equiv.Perm.permMatrix A (swapPerm p.1)) := by
        noncomm_ring
    _ = Equiv.Perm.permMatrix A (swapPerm p.1) * kronMat p.2 p.2 := by rw [hS, Matrix.mul_one]

/-- The averaging operator `(1 + ε·S)/2` is idempotent whenever `S * S = 1` and `ε * ε = 1`. -/
theorem s2p_proj_idem (hA : ∀ x y : A, x * y = y * x) (ε : ℂ) (hε : ε * ε = 1) {m : ℕ}
    {S : Matrix (Fin m) (Fin m) A} (hS : S * S = 1) :
    (algebraMap ℂ A (1/2) • (1 + algebraMap ℂ A ε • S)) *
      (algebraMap ℂ A (1/2) • (1 + algebraMap ℂ A ε • S)) =
    algebraMap ℂ A (1/2) • (1 + algebraMap ℂ A ε • S) := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  have hd : algebraMap ℂ A ε * algebraMap ℂ A ε = 1 := by rw [← map_mul, hε, map_one]
  have hT : (1 + algebraMap ℂ A ε • S) * (1 + algebraMap ℂ A ε • S) =
      (2:A) • (1 + algebraMap ℂ A ε • S) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hd, hS, one_smul]
    rw [smul_add, two_smul A (1 : Matrix (Fin m) (Fin m) A),
      two_smul A (algebraMap ℂ A ε • S)]
    abel
  have hc : algebraMap ℂ A (1/2) * algebraMap ℂ A (1/2) * (2:A) = algebraMap ℂ A (1/2) := by
    rw [show (2:A) = algebraMap ℂ A (2:ℂ) from (map_natCast (algebraMap ℂ A) 2).symm,
      ← map_mul, ← map_mul]
    norm_num
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hT, smul_smul, hc]

/-- `p ⊗ p` commutes with the averaging operator, since it commutes with the swap. -/
theorem s2p_kronMat_scalar_comm (hA : ∀ x y : A, x * y = y * x) (ε : ℂ) {p : Mat A}
    (hMS : kronMat p.2 p.2 * Equiv.Perm.permMatrix A (swapPerm p.1) =
      Equiv.Perm.permMatrix A (swapPerm p.1) * kronMat p.2 p.2) :
    kronMat p.2 p.2 *
        (algebraMap ℂ A (1/2) •
          (1 + algebraMap ℂ A ε • Equiv.Perm.permMatrix A (swapPerm p.1))) =
      (algebraMap ℂ A (1/2) •
          (1 + algebraMap ℂ A ε • Equiv.Perm.permMatrix A (swapPerm p.1))) *
        kronMat p.2 p.2 := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul,
    Matrix.smul_mul, hMS]

/-- A product of two commuting idempotents is idempotent. -/
theorem s2p_idem_mul_of_comm {m : ℕ} {M E : Matrix (Fin m) (Fin m) A} (hM : M * M = M)
    (hE : E * E = E) (hME : M * E = E * M) : (M * E) * (M * E) = M * E := by
  calc (M * E) * (M * E) = M * (E * M) * E := by noncomm_ring
    _ = M * (M * E) * E := by rw [← hME]
    _ = (M * M) * (E * E) := by noncomm_ring
    _ = M * E := by rw [hM, hE]

end Algebra

end


/-! ## The main lemma -/

/-- **`sq2Part ε p` is idempotent when `ε² = 1`.** -/
theorem sq2Part_idem {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (ε : ℂ) (hε : ε * ε = 1) {p : Mat A} (hp : p.IsIdem) : (sq2Part ε p).IsIdem := by
  have hS : (swapPerm p.1).permMatrix A * (swapPerm p.1).permMatrix A = 1 :=
    s2p_permMatrix_swapPerm_mul_self (A := A) p.1
  have hM : kronMat p.2 p.2 * kronMat p.2 p.2 = kronMat p.2 p.2 :=
    Mat.isIdem_kron hA hp hp
  have hMS : kronMat p.2 p.2 * (swapPerm p.1).permMatrix A =
      (swapPerm p.1).permMatrix A * kronMat p.2 p.2 := s2p_kronMat_swapPerm_comm hA p
  have hE : (algebraMap ℂ A (1/2) • (1 + algebraMap ℂ A ε • (swapPerm p.1).permMatrix A)) *
      (algebraMap ℂ A (1/2) • (1 + algebraMap ℂ A ε • (swapPerm p.1).permMatrix A)) =
      algebraMap ℂ A (1/2) • (1 + algebraMap ℂ A ε • (swapPerm p.1).permMatrix A) :=
    s2p_proj_idem hA ε hε hS
  have hME := s2p_kronMat_scalar_comm hA ε hMS
  exact s2p_idem_mul_of_comm hM hE hME

end Work.KT.Psi

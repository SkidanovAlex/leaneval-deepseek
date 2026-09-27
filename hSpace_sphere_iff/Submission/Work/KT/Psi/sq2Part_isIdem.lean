import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.swapPerm_permMatrix_sq

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/KT/DESIGN.md 'Addendum: psi'. SHARED helper needed by psi_exists (H8) and psi_comm (H6). CONVENTION: [Ring A] + explicit commutativity, never [CommRing A].
Proof: τ commutes with p⊗p and τ² = 1, so ((p⊗p)(1+ετ)/2)² = (p⊗p)(1+2ετ+ε²)/4 = sq2Part ε p for ε² = 1.
-/

namespace Work.KT.Psi

open Matrix

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The `A`-scalar action on matrices agrees with the `ℂ`-scalar action through `algebraMap`. -/
lemma alg_smul_eq (c : ℂ) {m n : Type} (X : Matrix m n A) :
    algebraMap ℂ A c • X = c • X := by
  ext i j
  simp only [Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]

/-- `reindex` is multiplicative. -/
lemma reindex_mul_helper {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (X Y : Matrix ι ι A) :
    Matrix.reindex e e (X * Y) =
      Matrix.reindex e e X * Matrix.reindex e e Y := by
  simpa only [Matrix.coe_reindexRingEquiv] using
    map_mul (Matrix.reindexRingEquiv A e) X Y

/-- The swap of the two factors of `Fin n × Fin n` commutes with the Kronecker square `M ⊗ M`. -/
lemma prodComm_kronMap_comm (hA : ∀ x y : A, x * y = y * x) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) :
    Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)) *
        Matrix.kroneckerMap (· * ·) M M =
      Matrix.kroneckerMap (· * ·) M M *
        Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)) := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  have hlhs : (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)) *
        Matrix.kroneckerMap (· * ·) M M) (i, j) (i', j') = M j i' * M i j' := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (j, i)]
    · rw [Work.KT.permMatrix_apply', if_pos (by rfl), Matrix.kroneckerMap_apply, one_mul]
    · intro b _ hb
      rw [Work.KT.permMatrix_apply', if_neg (fun h => hb h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hrhs : (Matrix.kroneckerMap (· * ·) M M *
        Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n))) (i, j) (i', j') =
        M i j' * M j i' := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (j', i')]
    · rw [Work.KT.permMatrix_apply', if_pos (by rfl), mul_one, Matrix.kroneckerMap_apply]
    · intro b _ hb
      rw [Work.KT.permMatrix_apply', if_neg (fun h => by
        rw [Equiv.prodComm_apply] at h
        exact hb (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hlhs, hrhs, hA]

/-- `swapPerm`'s permutation matrix commutes with the Kronecker square `M ⊗ M`. -/
lemma swap_kronMat_comm (hA : ∀ x y : A, x * y = y * x) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) :
    Work.KT.kronMat M M * (swapPerm n).permMatrix A =
      (swapPerm n).permMatrix A * Work.KT.kronMat M M := by
  simp only [Work.KT.kronMat]
  rw [← Work.KT.reindex_permMatrix_prodComm (A := A) n]
  rw [← reindex_mul_helper (A := A) finProdFinEquiv
        (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)))
        (Matrix.kroneckerMap (· * ·) M M),
      ← reindex_mul_helper (A := A) finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) M M)
        (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)))]
  rw [prodComm_kronMap_comm hA M]

/-- The projector `(1 + ε S)/2` on the `+`-part of an involution `S` is idempotent. -/
lemma proj2_orth_eps {m : ℕ}
    (K S : Matrix (Fin m) (Fin m) A) (hK : K * K = K) (hS : S * S = 1) (hKS : K * S = S * K)
    (ε : ℂ) (hε : ε * ε = 1) :
    (K * ((1 / 2 : ℂ) • (1 + ε • S))) * (K * ((1 / 2 : ℂ) • (1 + ε • S))) =
      K * ((1 / 2 : ℂ) • (1 + ε • S)) := by
  have hKT : K * ((1 / 2 : ℂ) • (1 + ε • S)) = ((1 / 2 : ℂ) • (1 + ε • S)) * K := by
    have h : K * (1 + ε • S) = (1 + ε • S) * K := by
      rw [mul_add, mul_one, add_mul, one_mul]
      congr 1
      rw [Matrix.mul_smul, Matrix.smul_mul, hKS]
    rw [Matrix.mul_smul, Matrix.smul_mul, h]
  have hTT : ((1 / 2 : ℂ) • (1 + ε • S)) * ((1 / 2 : ℂ) • (1 + ε • S)) =
      (1 / 2 : ℂ) • (1 + ε • S) := by
    have h : (1 + ε • S) * (1 + ε • S) = (2 : ℂ) • (1 + ε • S) := by
      have hSS : (ε • S) * (ε • S) = 1 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε, one_smul, hS]
      rw [mul_add, mul_one, add_mul, one_mul, hSS, two_smul]; abel
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul]; norm_num
  calc (K * ((1 / 2 : ℂ) • (1 + ε • S))) * (K * ((1 / 2 : ℂ) • (1 + ε • S)))
      = K * (((1 / 2 : ℂ) • (1 + ε • S)) * K) * ((1 / 2 : ℂ) • (1 + ε • S)) := by
        noncomm_ring
    _ = K * (K * ((1 / 2 : ℂ) • (1 + ε • S))) * ((1 / 2 : ℂ) • (1 + ε • S)) := by rw [← hKT]
    _ = (K * K) * (((1 / 2 : ℂ) • (1 + ε • S)) * ((1 / 2 : ℂ) • (1 + ε • S))) := by
        noncomm_ring
    _ = K * ((1 / 2 : ℂ) • (1 + ε • S)) := by rw [hK, hTT]

/-- `sq2Part ε p` is idempotent for `ε = ±1` (the swap commutes with `p ⊗ p` and squares to `1`). -/
theorem sq2Part_isIdem (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Mat A) (hp : p.IsIdem) (ε : ℂ) (hε : ε ^ 2 = 1) : (sq2Part ε p).IsIdem := by
  obtain ⟨n, P⟩ := p
  have hε' : ε * ε = 1 := by rw [← pow_two]; exact hε
  have hKK : Work.KT.kronMat P P * Work.KT.kronMat P P = Work.KT.kronMat P P :=
    Work.KT.Mat.isIdem_kron hA hp hp
  have hSS : (swapPerm n).permMatrix A * (swapPerm n).permMatrix A = 1 :=
    swapPerm_permMatrix_sq n
  have hKS : Work.KT.kronMat P P * (swapPerm n).permMatrix A =
      (swapPerm n).permMatrix A * Work.KT.kronMat P P := swap_kronMat_comm hA P
  change (Work.KT.kronMat P P * (algebraMap ℂ A (1 / 2) •
            (1 + algebraMap ℂ A ε • (swapPerm n).permMatrix A))) *
          (Work.KT.kronMat P P * (algebraMap ℂ A (1 / 2) •
            (1 + algebraMap ℂ A ε • (swapPerm n).permMatrix A))) =
        Work.KT.kronMat P P * (algebraMap ℂ A (1 / 2) •
            (1 + algebraMap ℂ A ε • (swapPerm n).permMatrix A))
  rw [alg_smul_eq (A := A) ε ((swapPerm n).permMatrix A),
      alg_smul_eq (A := A) (1 / 2) (1 + ε • (swapPerm n).permMatrix A)]
  exact proj2_orth_eps (Work.KT.kronMat P P) ((swapPerm n).permMatrix A) hKK hSS hKS ε hε'

end Work.KT.Psi

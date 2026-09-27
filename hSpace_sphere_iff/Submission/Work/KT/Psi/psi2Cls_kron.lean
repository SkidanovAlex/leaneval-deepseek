import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.sq2Part_idem
import Submission.Work.KT.Psi.sq2Part_split
import Submission.Work.KT.Psi.mulCls_comm
import Submission.Work.KT.Psi.cls_split
import Submission.Work.KT.Psi.cls_conj
import Submission.Work.KT.Psi.cls_orbit
import Submission.Work.KT.Psi.k3Aux
import Submission.Work.KT.Psi.kronAux
import Submission.Work.KT.Psi.clsM_idem_add
import Submission.Work.KT.Psi.psi2sum_Setup

/-!
# `Work.KT.Psi.psi2Cls_kron` — multiplicativity of `ψ²` on generators

`ψ²` on a generator `[p]` is `[Sym² p] − [Λ² p] = cls (sq2Part 1 p) − cls (sq2Part (-1) p)`, where
`sq2Part ε p` is `p ⊗ p` cut down by the projector `(1 + ε·σ)/2` of the swap `σ` of the two tensor
factors.  This file proves that `ψ²` is multiplicative on generators,

`ψ²(p ⊗ q) = ψ²(p) · ψ²(q)`,

expanded into the four classes `[sq2Part σ p ⊗ sq2Part τ q]`.

## The proof

Everything happens on the tensor square `(p ⊗ q) ⊗ (p ⊗ q)`, which the "middle four" exchange
`midPerm` rewrites as `(p ⊗ p) ⊗ (q ⊗ q)`.  There the swap of the two outer factors becomes the
product `S_p · S_q` of the swaps of the two inner factors, and the projector
`(1 + ε S_p S_q)/2` factors as

`(1 + S_p S_q)/2 = P⁺_p P⁺_q + P⁻_p P⁻_q`,  `(1 − S_p S_q)/2 = P⁺_p P⁻_q + P⁻_p P⁺_q`,

`P^{σ} = (1 + σ S)/2`.  Multiplying by `(p ⊗ p) ⊗ (q ⊗ q)` distributes over the two summands, and
each summand is `sq2Part σ p ⊗ sq2Part τ q`.  The two summands are orthogonal idempotents, so
their classes add (`clsM_idem_add`).

* `reindex_xiToOm_kron`, `reindex_xiToOm_permComm`: the two matrix identities expressing the
  middle-four exchange (`(A⊗B)⊗(C⊗D) ↦ (A⊗C)⊗(B⊗D)` for the tensor square, and the transporter of
  the swap).
* `projE_kroneckerMap`: the factorization of the projector on a tensor product.
* `sq2PartP_kron_pos`, `sq2PartP_kron_neg`: the two decompositions of `sq2Part (±1) (p ⊗ q)`.
* `cls_sq2Part_kron_pos`, `cls_sq2Part_kron_neg`: their `K₀`-forms.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-! ## The projector `(1 + ε S)/2` in `ℂ`-scalar form, and functoriality in the index type -/

/-- `projE ε S = (1/2) • (1 + ε • S)`, with the scalar action of `ℂ`. -/
theorem projE_eq_smul {A : Type} [Ring A] [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (S : Matrix ι ι A) : projE c S = (1/2:ℂ) • (1 + c • S) := by
  rw [projE, ← K3.smulC_eq_smulA (1/2) (1 + algebraMap ℂ A c • S),
    ← K3.smulC_eq_smulA c S]

/-- `reindex` commutes with `projE`. -/
theorem reindex_projE {A : Type} [Ring A] [Algebra ℂ A] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (c : ℂ) (Z : Matrix ι ι A) :
    Matrix.reindex e e (projE c Z) = projE c (Matrix.reindex e e Z) := by
  rw [projE, projE, Work.KT.reindex_smul, Work.KT.reindex_add',
    Work.KT.reindex_one', Work.KT.reindex_smul]

/-! ## The factorization of the projector on a tensor product -/

/-- **The symmetric projector on a tensor square.**  `(Sym ⊗ Sym) ⊕ (Λ ⊗ Λ)` is the symmetric part
of the tensor square, and `(Sym ⊗ Λ) ⊕ (Λ ⊗ Sym)` the antisymmetric part.  Here `Sym`/`Λ` are the
projectors `(1 ± σ)/2` of an arbitrary matrix `S = X ⊗ Y` of the tensor product, so no involution
hypothesis is needed — the cross terms cancel between the two summands. -/
theorem projE_kroneckerMap {A : Type} [Ring A] [Algebra ℂ A] {ι κ : Type} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (X : Matrix ι ι A) (Y : Matrix κ κ A)
    (ε σ₁ σ₂ : ℂ) (h : σ₁ * σ₂ = ε) :
    projE ε (Matrix.kroneckerMap (· * ·) X Y) =
      Matrix.kroneckerMap (· * ·) (projE σ₁ X) (projE σ₂ Y) +
      Matrix.kroneckerMap (· * ·) (projE (-σ₁) X) (projE (-σ₂) Y) := by
  have haa : (2:A)*(algebraMap ℂ A) (1/2)*(algebraMap ℂ A) (1/2) = (algebraMap ℂ A) (1/2) := by
    rw [show (2:A) = algebraMap ℂ A 2 from (map_ofNat (algebraMap ℂ A) 2).symm,
      ← map_mul, ← map_mul]
    norm_num
  have hhalf : ∀ B : A, (B+B)*((algebraMap ℂ A) (1/2)*(algebraMap ℂ A) (1/2))
      = (algebraMap ℂ A) (1/2)*B := by
    intro B
    rw [← two_mul B, mul_assoc,
      show (2:A)*(B*((algebraMap ℂ A) (1/2)*(algebraMap ℂ A) (1/2)))
        = B*((2:A)*(algebraMap ℂ A) (1/2)*(algebraMap ℂ A) (1/2)) from by noncomm_ring,
      show B*((2:A)*(algebraMap ℂ A) (1/2)*(algebraMap ℂ A) (1/2)) = B*(algebraMap ℂ A) (1/2)
        from by rw [haa],
      Algebra.commutes]
  have entry : ∀ (s1 s2 x y d1 d2 : A), (∀ z, s2 * z = z * s2) →
      (algebraMap ℂ A) (1/2) * (d1*d2 + s1*s2*(x*y)) =
        (algebraMap ℂ A) (1/2)*(d1+s1*x)*((algebraMap ℂ A) (1/2)*(d2+s2*y)) +
        (algebraMap ℂ A) (1/2)*(d1-s1*x)*((algebraMap ℂ A) (1/2)*(d2-s2*y)) := by
    intro s1 s2 x y d1 d2 h2
    have key : (s1*x)*(s2*y) = s1*s2*(x*y) := by
      calc (s1*x)*(s2*y) = s1*(x*s2)*y := by noncomm_ring
        _ = s1*(s2*x)*y := by rw [(h2 x).symm]
        _ = s1*s2*(x*y) := by noncomm_ring
    have e1 : (algebraMap ℂ A) (1/2)*(d1+s1*x)*((algebraMap ℂ A) (1/2)*(d2+s2*y))
        = (d1+s1*x)*(d2+s2*y)*((algebraMap ℂ A) (1/2)*(algebraMap ℂ A) (1/2)) := by
      rw [Algebra.commutes (1/2) (d1+s1*x), Algebra.commutes (1/2) (d2+s2*y)]
      rw [mul_assoc (d1+s1*x) _ ((d2+s2*y)*_),
        ← mul_assoc (algebraMap ℂ A (1/2)) (d2+s2*y) _, Algebra.commutes (1/2) (d2+s2*y)]
      noncomm_ring
    have e2 : (algebraMap ℂ A) (1/2)*(d1-s1*x)*((algebraMap ℂ A) (1/2)*(d2-s2*y))
        = (d1-s1*x)*(d2-s2*y)*((algebraMap ℂ A) (1/2)*(algebraMap ℂ A) (1/2)) := by
      rw [Algebra.commutes (1/2) (d1-s1*x), Algebra.commutes (1/2) (d2-s2*y)]
      rw [mul_assoc (d1-s1*x) _ ((d2-s2*y)*_),
        ← mul_assoc (algebraMap ℂ A (1/2)) (d2-s2*y) _, Algebra.commutes (1/2) (d2-s2*y)]
      noncomm_ring
    rw [e1, e2, ← add_mul]
    have hw : (d1+s1*x)*(d2+s2*y) + (d1-s1*x)*(d2-s2*y)
        = (d1*d2 + s1*s2*(x*y)) + (d1*d2 + s1*s2*(x*y)) := by
      have hw1 : (d1+s1*x)*(d2+s2*y) = d1*d2 + d1*(s2*y) + (s1*x)*d2 + (s1*x)*(s2*y) := by
        noncomm_ring
      have hw2 : (d1-s1*x)*(d2-s2*y) =
          d1*d2 + (-(d1*(s2*y))) + (-((s1*x)*d2)) + (s1*x)*(s2*y) := by noncomm_ring
      rw [hw1, hw2, key]; noncomm_ring
    rw [hw, hhalf]
  ext i j
  simp only [projE, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  have hcell : (if i = j then (1:A) else 0)
      = (if i.1 = j.1 then (1:A) else 0) * (if i.2 = j.2 then (1:A) else 0) := by
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]
      by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2 <;> simp_all [Prod.ext_iff]
  rw [hcell, ← h, map_mul, map_neg, map_neg, neg_mul, neg_mul,
    ← sub_eq_add_neg, ← sub_eq_add_neg]
  exact entry _ _ _ _ _ _ (fun z => Algebra.commutes σ₂ z)

/-! ## The middle-four exchange -/

/-- The inverse of the middle-four exchange, evaluated on `Ω = (M × M) × (N × N)`. -/
theorem midPerm_symm_apply (M N : ℕ) (a b : Fin M) (c d : Fin N) :
    (midPerm M N).symm ((a,b),(c,d)) = ((a,c),(b,d)) := rfl

/-- `Ω = (M × M) × (N × N)` is `(M × N) × (M × N)` up to the canonical reindexings. -/
theorem prodCongr_trans_xiToOm {M N : ℕ} :
    (finProdFinEquiv.prodCongr finProdFinEquiv).trans (xiToOm M N) = midPerm M N := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨a,b⟩,c,d⟩ := x
  simp only [xiToOm, midPerm, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply]
  simp [Equiv.symm_apply_apply]

/-- **The transporter of the swap under the middle-four exchange.**  The swap of the two factors of
`Fin (M*N) × Fin (M*N)`, transported to `Ω = (Fin M × Fin M) × (Fin N × Fin N)`, is the product of
the two swaps. -/
theorem reindex_xiToOm_permComm {A : Type} [Ring A] (M N : ℕ) :
    Matrix.reindex (xiToOm M N) (xiToOm M N)
        (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin (M*N)) (Fin (M*N)))) =
      Matrix.kroneckerMap (· * ·)
        (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin M) (Fin M)))
        (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin N) (Fin N))) := by
  rw [Work.KT.reindex_permMatrix, K3.kroneckerMap_permMatrix]
  congr 1
  apply Equiv.ext
  intro x
  obtain ⟨⟨a,b⟩,c,d⟩ := x
  simp only [xiToOm, midPerm, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, Equiv.prodComm_apply]
  simp [Equiv.symm_apply_apply]

/-- **The middle-four exchange for the tensor square.**  `(A⊗B) ⊗ (C⊗D)` is `(A⊗C) ⊗ (B⊗D)` up to
a permutation of the index set. -/
theorem reindex_xiToOm_kron {A : Type} [Ring A] (hA : ∀ x y : A, x * y = y * x) {M N : ℕ}
    (P : Matrix (Fin M) (Fin M) A) (Q : Matrix (Fin N) (Fin N) A) :
    Matrix.reindex (xiToOm M N) (xiToOm M N)
        (Matrix.kroneckerMap (· * ·) (kronMat P Q) (kronMat P Q)) =
      Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) P P)
        (Matrix.kroneckerMap (· * ·) Q Q) := by
  rw [show kronMat P Q
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) P Q) from rfl]
  rw [Matrix.kroneckerMap_reindex]
  rw [reindex_reindex]
  rw [prodCongr_trans_xiToOm]
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext x y
  obtain ⟨⟨a,b⟩,c,d⟩ := x
  obtain ⟨⟨a',b'⟩,c',d'⟩ := y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    midPerm_symm_apply]
  ring

/-! ## `sq2PartP` as a product with `projE`, its idempotency and orthogonality -/

/-- `sq2PartP ε p` is the tensor square cut down by the projector `projE ε` of the swap. -/
theorem sq2PartP_eq {A : Type} [Ring A] [Algebra ℂ A] (ε : ℂ) (p : Mat A) :
    sq2PartP ε p = Matrix.kroneckerMap (· * ·) p.2 p.2 *
      projE ε (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1))) := rfl

/-- The projector `(1 + S)/2` of an involution commutes with a commuting idempotent `K`. -/
theorem projE_mul_comm {A : Type} [Ring A] [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι A) (hKS : K * S = S * K) (ε : ℂ) :
    K * projE ε S = projE ε S * K := by
  rw [projE_eq_smul ε S, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [mul_add, mul_one, add_mul, one_mul, Matrix.mul_smul, Matrix.smul_mul, hKS]

/-- **The two `ε = ±1` sectors are orthogonal.** -/
theorem projE_orth_gen {A : Type} [Ring A] [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι A) (hK : K * K = K) (hS : S * S = 1) (hKS : K * S = S * K) :
    (K * projE 1 S) * (K * projE (-1) S) = 0 ∧ (K * projE (-1) S) * (K * projE 1 S) = 0 := by
  have hKE : ∀ ε : ℂ, K * projE ε S = projE ε S * K := projE_mul_comm K S hKS
  have h1 : projE 1 S = (1/2:ℂ) • (1 + S) := by rw [projE_eq_smul, one_smul]
  have hm : projE (-1) S = (1/2:ℂ) • (1 - S) := by
    rw [projE_eq_smul, neg_one_smul, sub_eq_add_neg]
  have hmul : ∀ (c d : ℂ) (M N : Matrix ι ι A),
      (c • M) * (d • N) = (c * d) • (M * N) := by
    intro c d M N
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hP : (1 + S) * (1 - S) = 0 := by
    rw [mul_sub, mul_one, add_mul, one_mul, hS]; abel
  have hP' : (1 - S) * (1 + S) = 0 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hS]; abel
  have horth1 : projE 1 S * projE (-1) S = 0 := by rw [h1, hm, hmul, hP, smul_zero]
  have horth2 : projE (-1) S * projE 1 S = 0 := by rw [h1, hm, hmul, hP', smul_zero]
  constructor
  · calc (K * projE 1 S) * (K * projE (-1) S)
        = K * (projE 1 S * K) * projE (-1) S := by noncomm_ring
      _ = K * (K * projE 1 S) * projE (-1) S := by rw [← hKE 1]
      _ = (K * K) * (projE 1 S * projE (-1) S) := by noncomm_ring
      _ = 0 := by rw [hK, horth1, mul_zero]
  · calc (K * projE (-1) S) * (K * projE 1 S)
        = K * (projE (-1) S * K) * projE 1 S := by noncomm_ring
      _ = K * (K * projE (-1) S) * projE 1 S := by rw [← hKE (-1)]
      _ = (K * K) * (projE (-1) S * projE 1 S) := by noncomm_ring
      _ = 0 := by rw [hK, horth2, mul_zero]

/-- `sq2PartP ε p` is idempotent for `ε² = 1`. -/
theorem sq2PartP_idem {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (ε : ℂ) (hε : ε * ε = 1) {p : Mat A} (hp : p.IsIdem) :
    sq2PartP ε p * sq2PartP ε p = sq2PartP ε p := by
  have h := sq2Part_idem hA ε hε hp
  unfold Mat.IsIdem at h
  rw [Work.KT.sq2Part_eq] at h
  refine (Matrix.reindexRingEquiv A (finProdFinEquiv (m := p.1) (n := p.1))).injective ?_
  rw [map_mul]
  exact h

/-- `Matrix.mul_kronecker_mul` for arbitrary finite index types (the Mathlib version is already
stated for rectangular matrices; we only supply the `CommSemiring` structure). -/
theorem kron_mul_gen {A : Type} [Ring A] (hA : ∀ x y : A, x * y = y * x)
    {l m n l' m' n' : Type} [Fintype m] [Fintype m']
    (M : Matrix l m A) (N : Matrix m n A) (P : Matrix l' m' A) (Q : Matrix m' n' A) :
    Matrix.kroneckerMap (· * ·) (M * N) (P * Q) =
      Matrix.kroneckerMap (· * ·) M P * Matrix.kroneckerMap (· * ·) N Q := by
  letI : CommSemiring A := { ‹Ring A› with mul_comm := fun a b => hA a b }
  exact Matrix.mul_kronecker_mul M N P Q

/-- **`sq2PartP (±1) p` are orthogonal** for an idempotent `p`. -/
theorem sq2PartP_orth {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p : Mat A} (hp : p.IsIdem) :
    sq2PartP 1 p * sq2PartP (-1) p = 0 ∧ sq2PartP (-1) p * sq2PartP 1 p = 0 := by
  have hK : Matrix.kroneckerMap (· * ·) p.2 p.2 * Matrix.kroneckerMap (· * ·) p.2 p.2
      = Matrix.kroneckerMap (· * ·) p.2 p.2 := by
    rw [← kron_mul hA p.2 p.2 p.2 p.2, hp]
  have hinv : Equiv.prodComm (Fin p.1) (Fin p.1) * Equiv.prodComm (Fin p.1) (Fin p.1) = 1 := by
    ext x <;> simp
  have hS : Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)) *
      Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)) = 1 := by
    rw [← Matrix.permMatrix_mul, hinv, Matrix.permMatrix_one]
  have hKS := kroneckerMap_self_comm_prodComm hA p.2
  have horth := projE_orth_gen (Matrix.kroneckerMap (· * ·) p.2 p.2)
    (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1))) hK hS hKS
  exact horth

/-! ## The two decompositions of `sq2Part (±1) (p ⊗ q)` -/

/-- **The decomposition of `sq2Part ε (p ⊗ q)`.**  On the tensor square of `p ⊗ q`, the swap is the
product of the swaps of the two inner factors, so the `ε`-projector splits into the two pieces
`σ₁ σ₂ = ε`. -/
theorem sq2PartP_kron_reindex {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (ε σ₁ σ₂ : ℂ) (h : σ₁ * σ₂ = ε) :
    Matrix.reindex (xiToOm p.1 q.1) (xiToOm p.1 q.1) (sq2PartP ε (p.kron q)) =
      Matrix.kroneckerMap (· * ·) (sq2PartP σ₁ p) (sq2PartP σ₂ q) +
      Matrix.kroneckerMap (· * ·) (sq2PartP (-σ₁) p) (sq2PartP (-σ₂) q) := by
  rw [show sq2PartP ε (p.kron q) = Matrix.kroneckerMap (· * ·) (kronMat p.2 q.2)
      (kronMat p.2 q.2) * projE ε (Equiv.Perm.permMatrix A
        (Equiv.prodComm (Fin (p.1*q.1)) (Fin (p.1*q.1)))) from rfl]
  rw [Work.KT.reindex_mul', reindex_xiToOm_kron hA, reindex_projE, reindex_xiToOm_permComm,
    projE_kroneckerMap (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)))
      (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin q.1) (Fin q.1))) ε σ₁ σ₂ h, mul_add]
  congr 1
  · exact (kron_mul_gen hA (Matrix.kroneckerMap (· * ·) p.2 p.2)
      (projE σ₁ (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1))))
      (Matrix.kroneckerMap (· * ·) q.2 q.2)
      (projE σ₂ (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin q.1) (Fin q.1))))).symm
  · exact (kron_mul_gen hA (Matrix.kroneckerMap (· * ·) p.2 p.2)
      (projE (-σ₁) (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1))))
      (Matrix.kroneckerMap (· * ·) q.2 q.2)
      (projE (-σ₂) (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin q.1) (Fin q.1))))).symm

/-- The `ε = 1` decomposition: `Sym²(p ⊗ q) = Sym²p ⊗ Sym²q ⊕ Λ²p ⊗ Λ²q`. -/
theorem sq2PartP_kron_pos {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} :
    Matrix.reindex (xiToOm p.1 q.1) (xiToOm p.1 q.1) (sq2PartP 1 (p.kron q)) =
      Matrix.kroneckerMap (· * ·) (sq2PartP 1 p) (sq2PartP 1 q) +
      Matrix.kroneckerMap (· * ·) (sq2PartP (-1) p) (sq2PartP (-1) q) := by
  simpa using sq2PartP_kron_reindex hA (1:ℂ) 1 1 (by norm_num)

/-- The `ε = -1` decomposition: `Λ²(p ⊗ q) = Sym²p ⊗ Λ²q ⊕ Λ²p ⊗ Sym²q`. -/
theorem sq2PartP_kron_neg {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} :
    Matrix.reindex (xiToOm p.1 q.1) (xiToOm p.1 q.1) (sq2PartP (-1) (p.kron q)) =
      Matrix.kroneckerMap (· * ·) (sq2PartP 1 p) (sq2PartP (-1) q) +
      Matrix.kroneckerMap (· * ·) (sq2PartP (-1) p) (sq2PartP 1 q) := by
  simpa using sq2PartP_kron_reindex hA (-1:ℂ) 1 (-1) (by norm_num)

/-! ## The class of a Kronecker product in `K₀` -/

/-- `clsM` is invariant under reindexing. -/
theorem clsM_reindex_k2 {A : Type} [Ring A] {ι κ : Type} [Fintype ι] [Fintype κ]
    (g : ι ≃ κ) (M : Matrix ι ι A) :
    clsM κ (Matrix.reindex g g M) = clsM ι M := clsI_reindex g M

/-- The class of `sq2Part ε p` is that of the unreindexed matrix `sq2PartP ε p`. -/
theorem cls_sq2Part_eq_clsM {A : Type} [Ring A] [Algebra ℂ A] (ε : ℂ) (p : Mat A) :
    cls (sq2Part ε p) = clsM (Fin p.1 × Fin p.1) (sq2PartP ε p) := by
  rw [Work.KT.sq2Part_eq, clsM_eq_cls]
  exact cls_ofIdx_irrel (sq2PartP ε p) finProdFinEquiv
    (Fintype.equivFin (Fin p.1 × Fin p.1))

/-- The `K₀`-class of the Kronecker product on the product index type is that of `Mat.kron`. -/
theorem clsM_kroneckerMap {A : Type} [Ring A] {n m : ℕ}
    (B : Matrix (Fin n × Fin n) (Fin n × Fin n) A) (C : Matrix (Fin m × Fin m) (Fin m × Fin m) A) :
    clsM ((Fin n × Fin n) × (Fin m × Fin m)) (Matrix.kroneckerMap (· * ·) B C) =
      cls (Mat.kron (⟨n * n, Matrix.reindex finProdFinEquiv finProdFinEquiv B⟩ : Mat A)
        ⟨m * m, Matrix.reindex finProdFinEquiv finProdFinEquiv C⟩) := by
  have hkron : kronMat (Matrix.reindex finProdFinEquiv finProdFinEquiv B)
      (Matrix.reindex finProdFinEquiv finProdFinEquiv C)
      = Matrix.reindex (omToFin n m) (omToFin n m) (Matrix.kroneckerMap (· * ·) B C) := by
    rw [show kronMat _ _ = Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (Matrix.reindex finProdFinEquiv finProdFinEquiv B)
          (Matrix.reindex finProdFinEquiv finProdFinEquiv C)) from rfl]
    rw [Matrix.kroneckerMap_reindex, reindex_reindex]
    rfl
  have hkr : Mat.kron (⟨n * n, Matrix.reindex finProdFinEquiv finProdFinEquiv B⟩ : Mat A)
        ⟨m * m, Matrix.reindex finProdFinEquiv finProdFinEquiv C⟩
      = Mat.ofIdx (Matrix.kroneckerMap (· * ·) B C) ((n * n) * (m * m)) (omToFin n m) := by
    change (⟨(n * n) * (m * m), kronMat (Matrix.reindex finProdFinEquiv finProdFinEquiv B)
      (Matrix.reindex finProdFinEquiv finProdFinEquiv C)⟩ : Mat A) = _
    exact congrArg (fun M => (⟨(n * n) * (m * m), M⟩ : Mat A)) hkron
  rw [clsM_eq_cls, hkr]
  exact cls_ofIdx_irrel (Matrix.kroneckerMap (· * ·) B C) (Fintype.equivFin _) (omToFin n m)

/-! ## The `K₀`-forms of the two decompositions -/

/-- `K₀`-form of the `ε = 1` decomposition. -/
theorem cls_sq2Part_kron_pos {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    cls (sq2Part 1 (p.kron q)) =
      cls (Mat.kron (sq2Part 1 p) (sq2Part 1 q)) +
      cls (Mat.kron (sq2Part (-1) p) (sq2Part (-1) q)) := by
  rw [cls_sq2Part_eq_clsM (1) (p.kron q)]
  change clsM (Fin (p.1 * q.1) × Fin (p.1 * q.1)) (sq2PartP 1 (p.kron q)) = _
  rw [← clsM_reindex_k2 (xiToOm p.1 q.1) (sq2PartP 1 (p.kron q)), sq2PartP_kron_pos hA]
  have ip : (sq2PartP 1 p * sq2PartP 1 p = sq2PartP 1 p) := sq2PartP_idem hA 1 (by norm_num) hp
  have iq : (sq2PartP 1 q * sq2PartP 1 q = sq2PartP 1 q) := sq2PartP_idem hA 1 (by norm_num) hq
  have jp : (sq2PartP (-1) p * sq2PartP (-1) p = sq2PartP (-1) p) :=
    sq2PartP_idem hA (-1) (by norm_num) hp
  have jq : (sq2PartP (-1) q * sq2PartP (-1) q = sq2PartP (-1) q) :=
    sq2PartP_idem hA (-1) (by norm_num) hq
  rw [clsM_idem_add _ _
    (by rw [← kron_mul_gen hA (sq2PartP 1 p) (sq2PartP 1 p) (sq2PartP 1 q) (sq2PartP 1 q),
        ip, iq])
    (by rw [← kron_mul_gen hA (sq2PartP (-1) p) (sq2PartP (-1) p) (sq2PartP (-1) q)
        (sq2PartP (-1) q), jp, jq])
    (by rw [← kron_mul_gen hA (sq2PartP 1 p) (sq2PartP (-1) p) (sq2PartP 1 q) (sq2PartP (-1) q),
        (sq2PartP_orth hA hp).1, (sq2PartP_orth hA hq).1]; ext i j; simp)
    (by rw [← kron_mul_gen hA (sq2PartP (-1) p) (sq2PartP 1 p) (sq2PartP (-1) q) (sq2PartP 1 q),
        (sq2PartP_orth hA hp).2, (sq2PartP_orth hA hq).2]; ext i j; simp)]
  congr 1
  · rw [clsM_kroneckerMap, ← Work.KT.sq2Part_eq 1 p, ← Work.KT.sq2Part_eq 1 q]
  · rw [clsM_kroneckerMap, ← Work.KT.sq2Part_eq (-1) p, ← Work.KT.sq2Part_eq (-1) q]

/-- `K₀`-form of the `ε = -1` decomposition. -/
theorem cls_sq2Part_kron_neg {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    cls (sq2Part (-1) (p.kron q)) =
      cls (Mat.kron (sq2Part 1 p) (sq2Part (-1) q)) +
      cls (Mat.kron (sq2Part (-1) p) (sq2Part 1 q)) := by
  rw [cls_sq2Part_eq_clsM (-1) (p.kron q)]
  change clsM (Fin (p.1 * q.1) × Fin (p.1 * q.1)) (sq2PartP (-1) (p.kron q)) = _
  rw [← clsM_reindex_k2 (xiToOm p.1 q.1) (sq2PartP (-1) (p.kron q)), sq2PartP_kron_neg hA]
  have ip : (sq2PartP 1 p * sq2PartP 1 p = sq2PartP 1 p) := sq2PartP_idem hA 1 (by norm_num) hp
  have iq : (sq2PartP (-1) q * sq2PartP (-1) q = sq2PartP (-1) q) :=
    sq2PartP_idem hA (-1) (by norm_num) hq
  have jp : (sq2PartP (-1) p * sq2PartP (-1) p = sq2PartP (-1) p) :=
    sq2PartP_idem hA (-1) (by norm_num) hp
  have jq : (sq2PartP 1 q * sq2PartP 1 q = sq2PartP 1 q) := sq2PartP_idem hA 1 (by norm_num) hq
  rw [clsM_idem_add _ _
    (by rw [← kron_mul_gen hA (sq2PartP 1 p) (sq2PartP 1 p) (sq2PartP (-1) q) (sq2PartP (-1) q),
        ip, iq])
    (by rw [← kron_mul_gen hA (sq2PartP (-1) p) (sq2PartP (-1) p) (sq2PartP 1 q) (sq2PartP 1 q),
        jp, jq])
    (by rw [← kron_mul_gen hA (sq2PartP 1 p) (sq2PartP (-1) p) (sq2PartP (-1) q) (sq2PartP 1 q),
        (sq2PartP_orth hA hp).1, (sq2PartP_orth hA hq).2]; ext i j; simp)
    (by rw [← kron_mul_gen hA (sq2PartP (-1) p) (sq2PartP 1 p) (sq2PartP 1 q) (sq2PartP (-1) q),
        (sq2PartP_orth hA hp).2, (sq2PartP_orth hA hq).1]; ext i j; simp)]
  congr 1
  · rw [clsM_kroneckerMap, ← Work.KT.sq2Part_eq 1 p, ← Work.KT.sq2Part_eq (-1) q]
  · rw [clsM_kroneckerMap, ← Work.KT.sq2Part_eq (-1) p, ← Work.KT.sq2Part_eq 1 q]

/-! ## The main theorem -/

/-- **Multiplicativity of `ψ²` on generators.** -/
theorem psi2Cls_kron {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    psi2Cls (p.kron q) =
      mulCls (sq2Part 1 p) (sq2Part 1 q) - mulCls (sq2Part 1 p) (sq2Part (-1) q) -
        mulCls (sq2Part (-1) p) (sq2Part 1 q) + mulCls (sq2Part (-1) p) (sq2Part (-1) q) := by
  have hp1 : (sq2Part 1 p).IsIdem := sq2Part_idem hA 1 (by norm_num) hp
  have hp2 : (sq2Part (-1) p).IsIdem := sq2Part_idem hA (-1) (by norm_num) hp
  have hq1 : (sq2Part 1 q).IsIdem := sq2Part_idem hA 1 (by norm_num) hq
  have hq2 : (sq2Part (-1) q).IsIdem := sq2Part_idem hA (-1) (by norm_num) hq
  rw [show mulCls (sq2Part 1 p) (sq2Part 1 q)
        = cls (Mat.kron (sq2Part 1 p) (sq2Part 1 q)) from by rw [mulCls, if_pos ⟨hp1, hq1⟩],
      show mulCls (sq2Part 1 p) (sq2Part (-1) q)
        = cls (Mat.kron (sq2Part 1 p) (sq2Part (-1) q)) from by rw [mulCls, if_pos ⟨hp1, hq2⟩],
      show mulCls (sq2Part (-1) p) (sq2Part 1 q)
        = cls (Mat.kron (sq2Part (-1) p) (sq2Part 1 q)) from by rw [mulCls, if_pos ⟨hp2, hq1⟩],
      show mulCls (sq2Part (-1) p) (sq2Part (-1) q)
        = cls (Mat.kron (sq2Part (-1) p) (sq2Part (-1) q)) from by rw [mulCls, if_pos ⟨hp2, hq2⟩]]
  rw [psi2Cls, if_pos (Mat.isIdem_kron hA hp hq),
    cls_sq2Part_kron_pos hA hp hq, cls_sq2Part_kron_neg hA hp hq]
  abel

end

end Work.KT.Psi

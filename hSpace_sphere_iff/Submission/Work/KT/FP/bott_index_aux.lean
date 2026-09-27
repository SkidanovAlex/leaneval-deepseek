import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.mvN_conj
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.Laurent
import Submission.Work.KT.FP.PencilDefs

/-!
# `Work.KT.FP.bott_index_aux` — auxiliary vocabulary for the Bott index

Definitions shared by the proof of `Work.KT.FP.bott_index`:

* `constLU` — a matrix over `C(X, ℂ)` as a *constant* Laurent matrix, as a unit of the Laurent
  matrix ring.  Multiplication by `constLU M` is multiplication by a unit that is independent of
  `z`, which is the operation under which the Bott index is invariant (`lindAt_const_inv`).
* `blockLast` / `blockAll` — the block-diagonal matrices `diag(1, …, 1, M)` and `diag(M, …, M)` on
  the block index `Fin (d+1) × Fin n`, and their `Fin ((d+1)*n)`-reindexed forms
  `blockLastF` / `blockAllF`.  They realise the two invariance properties of the W linearisation
  (`wPenA`/`wPenB`) under multiplication by a constant unit
  (`Work.KT.FP.linBf_const_identities`).
* `preSeq` / `appSeq` — the extension of a coefficient sequence by a zero coefficient, on the left
  and on the right.  They mediate the change of degree bound in `lindAt_pad`.
* `cls_conj_unit` — conjugation of a matrix by a unit does not change its `K₀`-class.
* `unitPull`, `unitConst`, `unitEval`, `unitConcat` — the (non-continuous!) toolkit for unit
  homotopies over `Y × [0,1]`: pullback along a continuous map, the constant unit, evaluation at a
  time, and concatenation.  `unitConcat` is the *multiplicative* concatenation
  `H₁ · (slice 1 H₁)⁻¹ · H₂` — no gluing of piecewise definitions is needed, because only the two
  endpoint slices matter.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X]

/-! ## Constant Laurent matrices -/

/-- A matrix over `C(X, ℂ)` regarded as a matrix of constant Laurent polynomials. -/
def constLM (X : Type) [TopologicalSpace X] {n : ℕ} :
    Matrix (Fin n) (Fin n) C(X, ℂ) →+* Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)) :=
  RingHom.mapMatrix (LaurentPolynomial.C (R := C(X, ℂ)))

/-- The constant Laurent matrix of a *unit*, as a unit of the Laurent matrix ring. -/
def constLU (X : Type) [TopologicalSpace X] {n : ℕ}
    (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    (Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))ˣ :=
  Units.map (constLM X).toMonoidHom M

@[simp] lemma constLU_coe (n : ℕ) (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    ((constLU X M : (Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))ˣ) :
        Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) = constLM X (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :=
  rfl

@[simp] lemma constLM_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (a c : Fin n) :
    constLM X M a c = LaurentPolynomial.C (M a c) := rfl

@[simp] lemma laurentMap_constLM (n : ℕ) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (constLM X M).map (Work.KT.laurentMap X) = Work.KT.Fund.pullMat X M := by
  ext i j
  simp [Work.KT.Fund.pullMat, Work.KT.laurentMap_C, Work.KT.pullAlg]

/-- Coefficients of a constant Laurent matrix. -/
lemma coeff_constLM (n : ℕ) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (j : ℤ) :
    (fun a c : Fin n => (constLM X M a c).coeff j) = if j = 0 then M else 0 := by
  by_cases h : j = 0
  · subst h
    ext a c
    simp [LaurentPolynomial.C_apply]
  · ext a c
    simp [LaurentPolynomial.C_apply, h]

/-! ## Block-diagonal matrices -/

/-- The block-diagonal matrix `diag(1, …, 1, M)` on the block index `Fin (d+1) × Fin n`. -/
def blockLast (X : Type) [TopologicalSpace X] (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) :=
  fun i j => if i.1 = j.1 then (if (i.1 : ℕ) = d then M else 1) i.2 j.2 else 0

/-- The block-diagonal matrix `diag(M, …, M)` on the block index `Fin (d+1) × Fin n`. -/
def blockAll (X : Type) [TopologicalSpace X] (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) C(X, ℂ) :=
  fun i j => if i.1 = j.1 then M i.2 j.2 else 0

/-- `blockLast`, reindexed to `Fin ((d+1)*n)`. -/
def blockLastF (X : Type) [TopologicalSpace X] (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X, ℂ) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (blockLast X n d M)

/-- `blockAll`, reindexed to `Fin ((d+1)*n)`. -/
def blockAllF (X : Type) [TopologicalSpace X] (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X, ℂ) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (blockAll X n d M)

/-! ## Extending a coefficient sequence by a zero -/

/-- Prepend a zero coefficient to a coefficient sequence. -/
def preSeq (X : Type) [TopologicalSpace X] (n : ℕ) {d : ℕ}
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Fin (d + 2) → Matrix (Fin n) (Fin n) C(X, ℂ) :=
  Fin.cases 0 b

/-- Append a zero coefficient to a coefficient sequence. -/
def appSeq (X : Type) [TopologicalSpace X] (n : ℕ) {d : ℕ}
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Fin (d + 2) → Matrix (Fin n) (Fin n) C(X, ℂ) :=
  fun j => if h : (j : ℕ) < d + 1 then b ⟨(j : ℕ), h⟩ else 0

/-! ## The block-diagonal matrices are multiplicative -/

lemma blockAllF_eq_kron (X : Type) [TopologicalSpace X] (n d : ℕ)
    (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    blockAllF X n d M = kronMatR (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) C(X, ℂ)) M := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ : ∃ p : Fin (d + 1) × Fin n, finProdFinEquiv p = i :=
    ⟨finProdFinEquiv.symm i, finProdFinEquiv.apply_symm_apply i⟩
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ : ∃ p : Fin (d + 1) × Fin n, finProdFinEquiv p = j :=
    ⟨finProdFinEquiv.symm j, finProdFinEquiv.apply_symm_apply j⟩
  rw [kronMatR_apply]
  simp only [blockAllF, blockAll, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : i₁ = j₁ <;> simp [h]

lemma blockAllF_one (X : Type) [TopologicalSpace X] (n d : ℕ) :
    blockAllF X n d (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) = 1 := by
  rw [blockAllF_eq_kron]
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ : ∃ p : Fin (d + 1) × Fin n, finProdFinEquiv p = i :=
    ⟨finProdFinEquiv.symm i, finProdFinEquiv.apply_symm_apply i⟩
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ : ∃ p : Fin (d + 1) × Fin n, finProdFinEquiv p = j :=
    ⟨finProdFinEquiv.symm j, finProdFinEquiv.apply_symm_apply j⟩
  rw [kronMatR_apply]
  by_cases h : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [h, h2, Matrix.one_apply]

lemma blockAllF_mul (X : Type) [TopologicalSpace X] (n d : ℕ)
    (M N : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    blockAllF X n d M * blockAllF X n d N = blockAllF X n d (M * N) := by
  rw [blockAllF_eq_kron, blockAllF_eq_kron, ← kronMatR_mul (fun x y : C(X, ℂ) => mul_comm x y),
    blockAllF_eq_kron]
  simp

lemma blockAllF_mul_inv (X : Type) [TopologicalSpace X] (n d : ℕ)
    (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    blockAllF X n d (M : Matrix (Fin n) (Fin n) C(X, ℂ))
        * blockAllF X n d (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ)) = 1 := by
  rw [blockAllF_mul, Units.mul_inv]
  exact blockAllF_one X n d

lemma blockAllF_inv_mul (X : Type) [TopologicalSpace X] (n d : ℕ)
    (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    blockAllF X n d (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
        * blockAllF X n d (M : Matrix (Fin n) (Fin n) C(X, ℂ)) = 1 := by
  rw [blockAllF_mul, Units.inv_mul]
  exact blockAllF_one X n d

/-- The inverse of the block-diagonal matrix `blockAllF M`, in the explicit form `blockAllF M⁻¹`. -/
lemma ringInverse_blockAllF (X : Type) [TopologicalSpace X] (n d : ℕ)
    (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    Ring.inverse (blockAllF X n d (M : Matrix (Fin n) (Fin n) C(X, ℂ)))
      = blockAllF X n d (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ)) := by
  have h := Ring.inverse_unit (⟨blockAllF X n d (M : Matrix (Fin n) (Fin n) C(X, ℂ)),
    blockAllF X n d (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ)),
    blockAllF_mul_inv X n d M, blockAllF_inv_mul X n d M⟩ :
      (Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X, ℂ))ˣ)
  simpa using h

/-! ## Coefficients of products with a constant Laurent matrix -/

/-- The coefficient of a finite sum of Laurent polynomials. -/
lemma coeff_finset_sum_lp {ι : Type*} {M : Type*} {R : Type*} [AddCommMonoid M] [Semiring R]
    (s : Finset ι) (f : ι → AddMonoidAlgebra R M) (m : M) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, ih]

section Coeff

variable {Z : Type} [TopologicalSpace Z]

lemma coeff_constLM_mul_lp (n : ℕ) (M : Matrix (Fin n) (Fin n) C(Z, ℂ))
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(Z, ℂ))) (i j : Fin n) (k : ℤ) :
    ((constLM Z M * P) i j).coeff k = ∑ a : Fin n, M i a * (P a j).coeff k := by
  rw [Matrix.mul_apply, coeff_finset_sum_lp]
  exact Finset.sum_congr rfl fun a _ => by
    rw [constLM_apply,
      show LaurentPolynomial.C (M i a) = AddMonoidAlgebra.single (0 : ℤ) (M i a) from rfl,
      AddMonoidAlgebra.coeff_single_zero_mul]

lemma coeff_mul_constLM_lp (n : ℕ) (M : Matrix (Fin n) (Fin n) C(Z, ℂ))
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(Z, ℂ))) (i j : Fin n) (k : ℤ) :
    ((P * constLM Z M) i j).coeff k = ∑ a : Fin n, (P i a).coeff k * M a j := by
  rw [Matrix.mul_apply, coeff_finset_sum_lp]
  exact Finset.sum_congr rfl fun a _ => by
    rw [constLM_apply,
      show LaurentPolynomial.C (M a j) = AddMonoidAlgebra.single (0 : ℤ) (M a j) from rfl,
      AddMonoidAlgebra.coeff_mul_single_zero]

lemma bound_constLM_mul_lp (n m : ℕ) (M : Matrix (Fin n) (Fin n) C(Z, ℂ))
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(Z, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0) :
    ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) →
      ((constLM Z M * P) i j).coeff k = 0 := by
  intro i j k hk
  rw [coeff_constLM_mul_lp]
  exact Finset.sum_eq_zero fun a _ => by rw [hb a j k hk, mul_zero]

lemma bound_mul_constLM_lp (n m : ℕ) (M : Matrix (Fin n) (Fin n) C(Z, ℂ))
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(Z, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0) :
    ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) →
      ((P * constLM Z M) i j).coeff k = 0 := by
  intro i j k hk
  rw [coeff_mul_constLM_lp]
  exact Finset.sum_eq_zero fun a _ => by rw [hb i a k hk, zero_mul]

end Coeff

/-! ## Conjugation by a unit -/

/-- Conjugation by a unit preserves idempotence. -/
lemma isIdem_conj {R : Type*} [Ring R] {e : R} (he : e * e = e) (u : Rˣ) :
    (↑u * e * ↑u⁻¹) * (↑u * e * ↑u⁻¹) = ↑u * e * ↑u⁻¹ := by
  have h2 : (↑u⁻¹ : R) * ↑u = 1 := Units.inv_mul u
  calc (↑u * e * ↑u⁻¹) * (↑u * e * ↑u⁻¹)
      = ↑u * (e * ((↑u⁻¹ * ↑u) * (e * ↑u⁻¹))) := by simp only [mul_assoc]
    _ = ↑u * (e * (1 * (e * ↑u⁻¹))) := by rw [h2]
    _ = ↑u * (e * (e * ↑u⁻¹)) := by rw [one_mul]
    _ = ↑u * (e * e) * ↑u⁻¹ := by simp only [mul_assoc]
    _ = ↑u * e * ↑u⁻¹ := by rw [he]

/-- Idempotence is preserved and reflected by conjugation by a unit. -/
lemma conj_idem_iff {R : Type*} [Ring R] (e : R) (u : Rˣ) :
    (↑u * e * ↑u⁻¹) * (↑u * e * ↑u⁻¹) = ↑u * e * ↑u⁻¹ ↔ e * e = e := by
  have h2 : (↑u⁻¹ : R) * ↑u = 1 := Units.inv_mul u
  have key : (↑u⁻¹ : R) * ((↑u * e * ↑u⁻¹) * (↑u * e * ↑u⁻¹)) * ↑u = e * e := by
    rw [show (↑u⁻¹ : R) * ((↑u * e * ↑u⁻¹) * (↑u * e * ↑u⁻¹)) * ↑u
        = (↑u⁻¹ * ↑u) * (e * ((↑u⁻¹ * ↑u) * (e * (↑u⁻¹ * ↑u)))) by simp only [mul_assoc]]
    simp [h2]
  have key2 : (↑u⁻¹ : R) * (↑u * e * ↑u⁻¹) * ↑u = e := by
    rw [show (↑u⁻¹ : R) * (↑u * e * ↑u⁻¹) * ↑u = (↑u⁻¹ * ↑u) * e * (↑u⁻¹ * ↑u) by
      simp only [mul_assoc]]
    simp [h2]
  refine ⟨fun h => ?_, fun h => isIdem_conj h u⟩
  calc e * e = (↑u⁻¹ : R) * ((↑u * e * ↑u⁻¹) * (↑u * e * ↑u⁻¹)) * ↑u := key.symm
    _ = (↑u⁻¹ : R) * (↑u * e * ↑u⁻¹) * ↑u := by rw [h]
    _ = e := key2

/-- **Conjugation by a unit does not change the `K₀`-class** of a matrix. -/
lemma cls_conj_unit {R : Type} [Ring R] {N : ℕ} (D : (Matrix (Fin N) (Fin N) R)ˣ)
    (P : Matrix (Fin N) (Fin N) R) :
    cls (⟨N, (D : Matrix (Fin N) (Fin N) R) * P * (↑D⁻¹ : Matrix (Fin N) (Fin N) R)⟩ : Mat R)
      = cls (⟨N, P⟩ : Mat R) := by
  by_cases hP : P * P = P
  · refine Work.KT.cls_eq_of_mvN (p := ⟨N, (D : Matrix (Fin N) (Fin N) R) * P
        * (↑D⁻¹ : Matrix (Fin N) (Fin N) R)⟩) (q := ⟨N, P⟩) (isIdem_conj hP D) hP ?_
    have hmvN := Work.KT.mvN_conj (E := D⁻¹) P hP
    rwa [inv_inv] at hmvN
  · have hne : ¬ ((D : Matrix (Fin N) (Fin N) R) * P * (↑D⁻¹ : Matrix (Fin N) (Fin N) R))
        * ((D : Matrix (Fin N) (Fin N) R) * P * (↑D⁻¹ : Matrix (Fin N) (Fin N) R))
        = (D : Matrix (Fin N) (Fin N) R) * P * (↑D⁻¹ : Matrix (Fin N) (Fin N) R) := by
      intro h
      exact hP ((conj_idem_iff P D).mp h)
    rw [Work.KT.cls_of_not_idem (p := ⟨N, (D : Matrix (Fin N) (Fin N) R) * P
          * (↑D⁻¹ : Matrix (Fin N) (Fin N) R)⟩) hne,
      Work.KT.cls_of_not_idem (p := ⟨N, P⟩) hP]

/-! ## The unit-homotopy toolkit -/

section Toolkit

variable {Y : Type} [TopologicalSpace Y]

/-- Pullback of a unit of matrices along a continuous map, as a monoid homomorphism. -/
def unitPullHom {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B)) (N : ℕ) :
    (Matrix (Fin N) (Fin N) C(B, ℂ))ˣ →* (Matrix (Fin N) (Fin N) C(A, ℂ))ˣ :=
  Units.map (RingHom.mapMatrix (Work.KT.pullAlg φ).toRingHom).toMonoidHom

/-- Pullback of a unit of matrices along a continuous map. -/
def unitPull {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B)) {N : ℕ}
    (H : (Matrix (Fin N) (Fin N) C(B, ℂ))ˣ) : (Matrix (Fin N) (Fin N) C(A, ℂ))ˣ :=
  unitPullHom φ N H

@[simp] lemma unitPull_mul {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B))
    {N : ℕ} (H K : (Matrix (Fin N) (Fin N) C(B, ℂ))ˣ) :
    unitPull φ (H * K) = unitPull φ H * unitPull φ K := map_mul _ _ _

@[simp] lemma unitPull_inv {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B))
    {N : ℕ} (H : (Matrix (Fin N) (Fin N) C(B, ℂ))ˣ) :
    unitPull φ H⁻¹ = (unitPull φ H)⁻¹ := map_inv _ _

@[simp] lemma unitPull_coe {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B))
    {N : ℕ} (H : (Matrix (Fin N) (Fin N) C(B, ℂ))ˣ) :
    ((unitPull φ H : (Matrix (Fin N) (Fin N) C(A, ℂ))ˣ) : Matrix (Fin N) (Fin N) C(A, ℂ))
      = (H : Matrix (Fin N) (Fin N) C(B, ℂ)).map ⇑(Work.KT.pullAlg φ) := rfl

@[simp] lemma unitPull_apply {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B))
    {N : ℕ} (H : (Matrix (Fin N) (Fin N) C(B, ℂ))ˣ) (i j : Fin N) (a : A) :
    (unitPull φ H : Matrix (Fin N) (Fin N) C(A, ℂ)) i j a
      = (H : Matrix (Fin N) (Fin N) C(B, ℂ)) i j (φ a) := rfl

/-- The unit of matrices which is constant in the second variable. -/
def unitConst {N : ℕ} (b : (Matrix (Fin N) (Fin N) C(Y, ℂ))ˣ) :
    (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ :=
  unitPull (ContinuousMap.fst : C(Y × unitInterval, Y)) b

/-- Evaluation of a unit homotopy at the time `t`. -/
def unitEval (t : unitInterval) {N : ℕ}
    (H : (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ) :
    (Matrix (Fin N) (Fin N) C(Y, ℂ))ˣ :=
  unitPull (ContinuousMap.prodMk (ContinuousMap.id Y) (ContinuousMap.const Y t)) H

@[simp] lemma unitEval_mul (t : unitInterval) {N : ℕ}
    (H K : (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ) :
    unitEval t (H * K) = unitEval t H * unitEval t K := map_mul _ _ _

@[simp] lemma unitEval_inv (t : unitInterval) {N : ℕ}
    (H : (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ) :
    unitEval t H⁻¹ = (unitEval t H)⁻¹ := map_inv _ _

@[simp] lemma unitEval_apply (t : unitInterval) {N : ℕ}
    (H : (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ) (i j : Fin N) (y : Y) :
    (unitEval t H : Matrix (Fin N) (Fin N) C(Y, ℂ)) i j y
      = (H : Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ)) i j (y, t) := rfl

@[simp] lemma unitEval_const (t : unitInterval) {N : ℕ} (b : (Matrix (Fin N) (Fin N) C(Y, ℂ))ˣ) :
    unitEval t (unitConst b) = b := by
  ext i j y
  rfl

/-- The *multiplicative* concatenation of two unit homotopies: `H₁ · (slice 1 H₁)⁻¹ · H₂`.  Its
slices at `0` and `1` are the slices of `H₁` at `0` and of `H₂` at `1`, provided the middle slices
match (this is the only thing the concatenation is used for). -/
def unitConcat {N : ℕ} (H₁ H₂ : (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ) :
    (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ :=
  H₁ * (unitConst (unitEval 1 H₁))⁻¹ * H₂

lemma unitEval_zero_unitConcat {N : ℕ}
    (H₁ H₂ : (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ)
    (h : unitEval 0 H₂ = unitEval 1 H₁) :
    unitEval 0 (unitConcat H₁ H₂) = unitEval 0 H₁ := by
  rw [unitConcat, unitEval_mul, unitEval_mul, unitEval_inv, unitEval_const, h]
  group

lemma unitEval_one_unitConcat {N : ℕ}
    (H₁ H₂ : (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ)
    (h : unitEval 0 H₂ = unitEval 1 H₁) :
    unitEval 1 (unitConcat H₁ H₂) = unitEval 1 H₂ := by
  rw [unitConcat, unitEval_mul, unitEval_mul, unitEval_inv, unitEval_const]
  group


/-! ## Reparametrisations of the unit interval -/

/-- The swap of the last two coordinates, `((x,t),z) ↦ ((x,z),t)`. -/
def swapCm (X : Type) [TopologicalSpace X] :
    C((X × unitInterval) × Sph ℂ, (X × Sph ℂ) × unitInterval) where
  toFun p := ((p.1.1, p.2), p.1.2)
  continuous_toFun := by fun_prop

/-- The time reversal `((x,z),t) ↦ ((x,z),1-t)`. -/
def revCm (X : Type) [TopologicalSpace X] :
    C((X × Sph ℂ) × unitInterval, (X × Sph ℂ) × unitInterval) where
  toFun p := (p.1, ⟨1 - (p.2 : ℝ), by
    refine ⟨by have := p.2.2.2; linarith, by have := p.2.2.1; linarith⟩⟩)
  continuous_toFun := by fun_prop

@[simp] lemma swapCm_apply {X : Type} [TopologicalSpace X] (p : (X × unitInterval) × Sph ℂ) :
    swapCm X p = ((p.1.1, p.2), p.1.2) := rfl

lemma revCm_zero {X : Type} [TopologicalSpace X] (p : X × Sph ℂ) :
    revCm X (p, 0) = (p, 1) := by
  simp [revCm]

lemma revCm_one {X : Type} [TopologicalSpace X] (p : X × Sph ℂ) :
    revCm X (p, 1) = (p, 0) := by
  simp [revCm]

variable {Y : Type} [TopologicalSpace Y] {N : ℕ}

/-- The slice at time `t` of the coordinate swap. -/
lemma unitPull_swapCm_apply
    (H : (Matrix (Fin N) (Fin N) C((Y × Sph ℂ) × unitInterval, ℂ))ˣ) (i j : Fin N)
    (x : Y) (t : unitInterval) (z : Sph ℂ) :
    (unitPull (swapCm Y) H : Matrix (Fin N) (Fin N) C((Y × unitInterval) × Sph ℂ, ℂ)) i j
        ((x, t), z)
      = (H : Matrix (Fin N) (Fin N) C((Y × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), t) := by
  rw [unitPull_apply]
  rfl

/-- The slice at `0` of the time-reversed homotopy is the slice at `1`. -/
lemma unitEval_zero_unitPull_rev
    (H : (Matrix (Fin N) (Fin N) C((Y × Sph ℂ) × unitInterval, ℂ))ˣ) :
    unitEval 0 (unitPull (revCm Y) H) = unitEval 1 H := by
  ext i j p
  obtain ⟨x, z⟩ := p
  rw [unitEval_apply, unitPull_apply, revCm_zero, unitEval_apply]

/-- The slice at `1` of the time-reversed homotopy is the slice at `0`. -/
lemma unitEval_one_unitPull_rev
    (H : (Matrix (Fin N) (Fin N) C((Y × Sph ℂ) × unitInterval, ℂ))ˣ) :
    unitEval 1 (unitPull (revCm Y) H) = unitEval 0 H := by
  ext i j p
  obtain ⟨x, z⟩ := p
  rw [unitEval_apply, unitPull_apply, revCm_one, unitEval_apply]


/-- A unit-valued slice equation implies the entrywise equation. -/
lemma unitEval_eq_entries {N : ℕ} (Y : Type) [TopologicalSpace Y] (t : unitInterval)
    (K : (Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ))ˣ)
    (a : (Matrix (Fin N) (Fin N) C(Y, ℂ))ˣ) (h : unitEval t K = a) :
    ∀ (i j : Fin N) (y : Y), (K : Matrix (Fin N) (Fin N) C(Y × unitInterval, ℂ)) i j (y, t)
      = (a : Matrix (Fin N) (Fin N) C(Y, ℂ)) i j y := by
  intro i j y
  have h1 : ((unitEval t K : (Matrix (Fin N) (Fin N) C(Y, ℂ))ˣ) : Matrix (Fin N) (Fin N) C(Y, ℂ))
      = ((a : (Matrix (Fin N) (Fin N) C(Y, ℂ))ˣ) : Matrix (Fin N) (Fin N) C(Y, ℂ)) :=
    congrArg (fun M : (Matrix (Fin N) (Fin N) C(Y, ℂ))ˣ =>
      (M : Matrix (Fin N) (Fin N) C(Y, ℂ))) h
  have h2 : (unitEval t K : Matrix (Fin N) (Fin N) C(Y, ℂ)) i j y
      = (a : Matrix (Fin N) (Fin N) C(Y, ℂ)) i j y := by
    rw [h1]
  simpa [unitEval_apply] using h2

end Toolkit

end

end Work.KT.FP

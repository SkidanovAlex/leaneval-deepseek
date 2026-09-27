import Mathlib
import Submission.Work.KT.FP.bott_index_aux
import Submission.Work.KT.FP.PencilDefs

/-!
# `Work.KT.FP.linBf_const_identities_bc`

Multiplication of the W-linearisation of a Laurent matrix by the block-diagonal constant matrices
`blockLast = diag(1, …, 1, M)` and `blockAll = diag(M, …, M)`:

* `blockLast · wPenA = wPenA` and `blockLast · wPenB c = wPenB (M · c)`: multiplication of the
  coefficient sequence on the *left* by a constant corresponds to multiplying the whole pencil on
  the left by `blockLast` (the `z`-coefficient `wPenA` is unchanged because its last block vanishes);
* `blockAll M · wPenA · blockAll M⁻¹ = wPenA` and
  `blockAll M · wPenB c · blockAll M⁻¹ = wPenB (M · c · M⁻¹)`: conjugation by `blockAll` acts on
  the pencil as conjugation of the coefficients by the constant matrix `M`.

The proofs reduce, through the ring isomorphism
`Matrix (D × n) (D × n) R ≃+* Matrix D D (Matrix n n R)` (`blkRingEquiv_bc`), to the corresponding
identities for `Matrix.diagonal`, and then transport along `Matrix.reindexRingEquiv`.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

set_option linter.unusedSectionVars false

/-! ## The "matrix of matrices" isomorphism -/

section BlkIso

variable {𝕜 : Type*} [CommRing 𝕜]

/-- Currying the two index coordinates: a matrix on `D × n` as a matrix on `D` whose entries are
matrices on `n`. -/
def blkEquivFun_bc {D n : Type} (M : Matrix (D × n) (D × n) 𝕜) : Matrix D D (Matrix n n 𝕜) :=
  fun i j => fun a b => M (i,a) (j,b)

/-- The inverse currying. -/
def blkEquivSymm_bc {D n : Type} (M : Matrix D D (Matrix n n 𝕜)) : Matrix (D × n) (D × n) 𝕜 :=
  fun p q => M p.1 q.1 p.2 q.2

variable {D n : Type} [Fintype D] [Fintype n] [DecidableEq D]

/-- `blkEquivFun_bc` as an equivalence. -/
def blkEquiv_bc : Matrix (D × n) (D × n) 𝕜 ≃ Matrix D D (Matrix n n 𝕜) where
  toFun := blkEquivFun_bc
  invFun := blkEquivSymm_bc
  left_inv M := by ext p q; rfl
  right_inv M := by ext i j a b; rfl

/-- **The block-matrix isomorphism** `Matrix (D × n) (D × n) 𝕜 ≃+* Matrix D D (Matrix n n 𝕜)`. -/
def blkRingEquiv_bc : Matrix (D × n) (D × n) 𝕜 ≃+* Matrix D D (Matrix n n 𝕜) :=
  RingEquiv.mk blkEquiv_bc (fun X Y => by
    ext i j a b
    simp only [blkEquiv_bc, blkEquivFun_bc, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.sum_apply]) (fun X Y => by
    ext i j a b
    simp only [blkEquiv_bc, blkEquivFun_bc, Matrix.add_apply])

@[simp] lemma blkRingEquiv_apply (M : Matrix (D × n) (D × n) 𝕜) (i j : D) (a b : n) :
    blkRingEquiv_bc M i j a b = M (i,a) (j,b) := rfl

/-- Applying an `if` to a matrix entry by entry. -/
lemma matrix_ite_apply_bc {m n : Type} {α : Type*} [Zero α] (P : Prop) [Decidable P]
    (A B : Matrix m n α) (i : m) (j : n) :
    (if P then A else B) i j = if P then A i j else B i j := by
  by_cases h : P <;> simp [h]

/-- The `z`-coefficient of the W-linearisation, in block form. -/
def pencilA_bc (n d : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) (Matrix (Fin n) (Fin n) 𝕜) :=
  fun i j => if i = j ∧ (i:ℕ) ≠ d then 1 else 0

/-- The constant coefficient of the W-linearisation, in block form. -/
def pencilB_bc (n d : ℕ) (c : Fin (d+1) → Matrix (Fin n) (Fin n) 𝕜) :
    Matrix (Fin (d+1)) (Fin (d+1)) (Matrix (Fin n) (Fin n) 𝕜) :=
  fun i j => if ((i:ℕ) + 1 = (j:ℕ)) then (if (i:ℕ) = d then c j else -1)
    else (if (i:ℕ) = d then c j else 0)

end BlkIso

/-! ## The images of the block-diagonal matrices and of the W-linearisation -/

section Images

variable (X : Type) [TopologicalSpace X]

lemma blkRingEquiv_blockLast (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X,ℂ)) :
    blkRingEquiv_bc (blockLast X n d M)
      = Matrix.diagonal (fun i : Fin (d+1) => if (i:ℕ) = d then M else 1) := by
  refine Matrix.ext (fun i j => ?_)
  refine Matrix.ext (fun a b => ?_)
  by_cases h : i = j
  · subst h; simp [blockLast]
  · simp [blockLast, h]

lemma blkRingEquiv_blockAll (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X,ℂ)) :
    blkRingEquiv_bc (blockAll X n d M) = Matrix.diagonal (fun _ : Fin (d+1) => M) := by
  refine Matrix.ext (fun i j => ?_)
  refine Matrix.ext (fun a b => ?_)
  by_cases h : i = j
  · subst h; simp [blockAll]
  · simp [blockAll, h]

lemma blkRingEquiv_wPenA (n d : ℕ) :
    blkRingEquiv_bc (wPenA X n d) = pencilA_bc n d := by
  refine Matrix.ext (fun i j => ?_)
  refine Matrix.ext (fun a b => ?_)
  by_cases h : i = j ∧ (i:ℕ) ≠ d <;>
    simp [wPenA, pencilA_bc, matrix_ite_apply_bc, h, Matrix.one_apply]

lemma blkRingEquiv_wPenB (n d : ℕ) (c : Fin (d+1) → Matrix (Fin n) (Fin n) C(X,ℂ)) :
    blkRingEquiv_bc (wPenB X n d c) = pencilB_bc n d c := by
  refine Matrix.ext (fun i j => ?_)
  refine Matrix.ext (fun a b => ?_)
  by_cases h : (i:ℕ) = d <;>
    simp [wPenB, pencilB_bc, matrix_ite_apply_bc, h, Matrix.neg_apply, Matrix.one_apply]

end Images

/-! ## The four block identities -/

section BlockIdentities

variable (X : Type) [TopologicalSpace X]

/-- Multiplying the W pencil on the left by `blockLast M` fixes the `z`-coefficient. -/
lemma blockLast_mul_wPenA_bc (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X,ℂ)) :
    blockLast X n d M * wPenA X n d = wPenA X n d := by
  apply blkRingEquiv_bc.injective
  rw [map_mul, blkRingEquiv_blockLast X, blkRingEquiv_wPenA X]
  refine Matrix.ext (fun i j => ?_)
  rw [Matrix.diagonal_mul]
  by_cases h : (i:ℕ) = d
  · have hBA : pencilA_bc (𝕜 := C(X,ℂ)) n d i j = 0 := by
      rw [pencilA_bc, if_neg]; rintro ⟨-, hd⟩; exact hd h
    rw [hBA, mul_zero]
  · have hD : (if (i:ℕ) = d then M else (1 : Matrix (Fin n) (Fin n) C(X,ℂ))) = 1 := by simp [h]
    rw [hD, one_mul]

/-- Multiplying the W pencil on the left by `blockLast M` multiplies the coefficients on the
left. -/
lemma blockLast_mul_wPenB_bc (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X,ℂ))
    (c : Fin (d+1) → Matrix (Fin n) (Fin n) C(X,ℂ)) :
    blockLast X n d M * wPenB X n d c = wPenB X n d (fun j => M * c j) := by
  apply blkRingEquiv_bc.injective
  rw [map_mul, blkRingEquiv_blockLast X, blkRingEquiv_wPenB X, blkRingEquiv_wPenB X]
  refine Matrix.ext (fun i j => ?_)
  rw [Matrix.diagonal_mul]
  by_cases h : (i:ℕ) = d
  · have hD : (if (i:ℕ) = d then M else (1 : Matrix (Fin n) (Fin n) C(X,ℂ))) = M := by simp [h]
    have h1 : pencilB_bc (𝕜 := C(X,ℂ)) n d c i j = c j := by
      have hj : (j:ℕ) < d + 1 := j.isLt
      simp only [pencilB_bc]; rw [if_neg (by omega), if_pos h]
    have h2 : pencilB_bc (𝕜 := C(X,ℂ)) n d (fun j => M * c j) i j = M * c j := by
      have hj : (j:ℕ) < d + 1 := j.isLt
      simp only [pencilB_bc]; rw [if_neg (by omega), if_pos h]
    rw [hD, h1, h2]
  · have hD : (if (i:ℕ) = d then M else (1 : Matrix (Fin n) (Fin n) C(X,ℂ))) = 1 := by simp [h]
    rw [hD, one_mul]
    simp [pencilB_bc, h]

/-- Conjugating the `z`-coefficient by `blockAll M` fixes it. -/
lemma blockAll_conj_wPenA_bc (n d : ℕ) (A B : Matrix (Fin n) (Fin n) C(X,ℂ)) (hAB : A * B = 1) :
    blockAll X n d A * wPenA X n d * blockAll X n d B = wPenA X n d := by
  apply blkRingEquiv_bc.injective
  rw [map_mul, map_mul, blkRingEquiv_blockAll X, blkRingEquiv_wPenA X, blkRingEquiv_blockAll X]
  refine Matrix.ext (fun i j => ?_)
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = j ∧ (i:ℕ) ≠ d
  · have hBA : pencilA_bc (𝕜 := C(X,ℂ)) n d i j = 1 := by rw [pencilA_bc, if_pos h]
    rw [hBA]
    show A * (1 : Matrix (Fin n) (Fin n) C(X,ℂ)) * B = (1 : Matrix (Fin n) (Fin n) C(X,ℂ))
    rw [mul_one, hAB]
  · have hBA : pencilA_bc (𝕜 := C(X,ℂ)) n d i j = 0 := by rw [pencilA_bc, if_neg h]
    rw [hBA]
    show A * (0 : Matrix (Fin n) (Fin n) C(X,ℂ)) * B = (0 : Matrix (Fin n) (Fin n) C(X,ℂ))
    rw [mul_zero, zero_mul]

/-- Conjugating the W pencil by `blockAll M` conjugates the coefficients by `M`. -/
lemma blockAll_conj_wPenB_bc (n d : ℕ) (A B : Matrix (Fin n) (Fin n) C(X,ℂ)) (hAB : A * B = 1)
    (c : Fin (d+1) → Matrix (Fin n) (Fin n) C(X,ℂ)) :
    blockAll X n d A * wPenB X n d c * blockAll X n d B
      = wPenB X n d (fun j => A * c j * B) := by
  apply blkRingEquiv_bc.injective
  rw [map_mul, map_mul, blkRingEquiv_blockAll X, blkRingEquiv_wPenB X, blkRingEquiv_blockAll X,
      blkRingEquiv_wPenB X]
  refine Matrix.ext (fun i j => ?_)
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : (i:ℕ) = d
  · have h1 : pencilB_bc (𝕜 := C(X,ℂ)) n d c i j = c j := by
      have hj : (j:ℕ) < d + 1 := j.isLt
      simp only [pencilB_bc]; rw [if_neg (by omega), if_pos h]
    have h2 : pencilB_bc (𝕜 := C(X,ℂ)) n d (fun j => A * c j * B) i j = A * c j * B := by
      have hj : (j:ℕ) < d + 1 := j.isLt
      simp only [pencilB_bc]; rw [if_neg (by omega), if_pos h]
    rw [h1, h2]
  · have h1 : pencilB_bc (𝕜 := C(X,ℂ)) n d c i j
        = (if ((i:ℕ)+1 = (j:ℕ)) then -1 else 0) := by simp [pencilB_bc, h]
    have h2 : pencilB_bc (𝕜 := C(X,ℂ)) n d (fun j => A * c j * B) i j
        = (if ((i:ℕ)+1 = (j:ℕ)) then -1 else 0) := by simp [pencilB_bc, h]
    rw [h1, h2]
    by_cases hc : (i:ℕ)+1 = (j:ℕ)
    · rw [if_pos hc]
      simp [hAB]
    · rw [if_neg hc]
      simp

end BlockIdentities

/-! ## The block-diagonal matrices are units -/

section Units

variable {𝕜 : Type*} [CommRing 𝕜] {D n : Type} [Fintype D] [DecidableEq D] [Fintype n]
  [DecidableEq n]

/-- A diagonal matrix all of whose entries are units is a unit. -/
lemma isUnit_diagonal_units_bc (u : D → (Matrix n n 𝕜)ˣ) :
    IsUnit (Matrix.diagonal (fun i => (u i : Matrix n n 𝕜))) := by
  refine ⟨{ val := Matrix.diagonal (fun i => (u i : Matrix n n 𝕜)),
            inv := Matrix.diagonal (fun i => ((u i)⁻¹ : (Matrix n n 𝕜)ˣ)),
            val_inv := ?_, inv_val := ?_ }, rfl⟩
  · rw [Matrix.diagonal_mul_diagonal]; simp only [Units.mul_inv, Matrix.diagonal_one]
  · rw [Matrix.diagonal_mul_diagonal]; simp only [Units.inv_mul, Matrix.diagonal_one]

end Units

section UnitsFP

variable (X : Type) [TopologicalSpace X]

lemma isUnit_blockAll_bc (n d : ℕ) (M : (Matrix (Fin n) (Fin n) C(X,ℂ))ˣ) :
    IsUnit (blockAll X n d (M : Matrix (Fin n) (Fin n) C(X,ℂ))) := by
  have h1 : IsUnit (Matrix.diagonal
      (fun _ : Fin (d+1) => (M : Matrix (Fin n) (Fin n) C(X,ℂ)))) :=
    isUnit_diagonal_units_bc (fun _ : Fin (d+1) => M)
  have h2 : blockAll X n d (M : Matrix (Fin n) (Fin n) C(X,ℂ))
      = blkRingEquiv_bc.symm (Matrix.diagonal
          (fun _ : Fin (d+1) => (M : Matrix (Fin n) (Fin n) C(X,ℂ)))) := by
    rw [← blkRingEquiv_blockAll X n d (M : Matrix (Fin n) (Fin n) C(X,ℂ))]; simp
  rw [h2]
  exact h1.map blkRingEquiv_bc.symm

lemma isUnit_blockLast_bc (n d : ℕ) (M : (Matrix (Fin n) (Fin n) C(X,ℂ))ˣ) :
    IsUnit (blockLast X n d (M : Matrix (Fin n) (Fin n) C(X,ℂ))) := by
  let u : Fin (d+1) → (Matrix (Fin n) (Fin n) C(X,ℂ))ˣ :=
    fun i => if (i:ℕ) = d then M else 1
  have hu : (fun i : Fin (d+1) => (u i : Matrix (Fin n) (Fin n) C(X,ℂ)))
      = fun i : Fin (d+1) =>
          (if (i:ℕ) = d then (M : Matrix (Fin n) (Fin n) C(X,ℂ)) else 1) := by
    funext i; by_cases h : (i:ℕ) = d <;> simp [u, h]
  have h1 : IsUnit (Matrix.diagonal (fun i => (u i : Matrix (Fin n) (Fin n) C(X,ℂ)))) :=
    isUnit_diagonal_units_bc u
  rw [hu] at h1
  have h2 : blockLast X n d (M : Matrix (Fin n) (Fin n) C(X,ℂ))
      = blkRingEquiv_bc.symm (Matrix.diagonal (fun i : Fin (d+1) =>
          if (i:ℕ) = d then (M : Matrix (Fin n) (Fin n) C(X,ℂ)) else 1)) := by
    rw [← blkRingEquiv_blockLast X n d (M : Matrix (Fin n) (Fin n) C(X,ℂ))]; simp
  rw [h2]
  exact h1.map blkRingEquiv_bc.symm

end UnitsFP

/-! ## Coefficients of products with a constant Laurent matrix -/

section Coeff

variable (X : Type) [TopologicalSpace X]

/-- The coefficient of a finite sum of Laurent polynomials. -/
lemma coeff_finset_sum_bc {ι : Type*} (s : Finset ι) (f : ι → LaurentPolynomial C(X,ℂ)) (m : ℤ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, ih]

/-- The coefficient of `C r * q`. -/
lemma coeff_C_mul_bc (r : C(X,ℂ)) (q : LaurentPolynomial C(X,ℂ)) (k : ℤ) :
    (LaurentPolynomial.C r * q).coeff k = r * q.coeff k := by
  rw [show LaurentPolynomial.C r = AddMonoidAlgebra.single (0 : ℤ) r from rfl,
    AddMonoidAlgebra.coeff_single_zero_mul]

/-- The coefficient of `q * C r`. -/
lemma coeff_mul_C_bc (r : C(X,ℂ)) (q : LaurentPolynomial C(X,ℂ)) (k : ℤ) :
    (q * LaurentPolynomial.C r).coeff k = q.coeff k * r := by
  rw [show LaurentPolynomial.C r = AddMonoidAlgebra.single (0 : ℤ) r from rfl,
    AddMonoidAlgebra.coeff_mul_single_zero]

lemma coeff_constLM_mul_bc (n : ℕ) (M : Matrix (Fin n) (Fin n) C(X,ℂ))
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X,ℂ))) (i j : Fin n) (k : ℤ) :
    ((constLM X M * P) i j).coeff k = ∑ a : Fin n, M i a * (P a j).coeff k := by
  rw [Matrix.mul_apply, coeff_finset_sum_bc X]
  exact Finset.sum_congr rfl fun a _ => by rw [constLM_apply, coeff_C_mul_bc X]

lemma coeff_mul_constLM_bc (n : ℕ) (M : Matrix (Fin n) (Fin n) C(X,ℂ))
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X,ℂ))) (i j : Fin n) (k : ℤ) :
    ((P * constLM X M) i j).coeff k = ∑ a : Fin n, (P i a).coeff k * M a j := by
  rw [Matrix.mul_apply, coeff_finset_sum_bc X]
  exact Finset.sum_congr rfl fun a _ => by rw [constLM_apply, coeff_mul_C_bc X]

/-- The coefficient sequence of `constLM A * P` is `A` times that of `P`. -/
lemma coeffSeq_mul_const_bc (n m : ℕ) (A : Matrix (Fin n) (Fin n) C(X,ℂ))
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X,ℂ))) (j : Fin (2*m+1)) :
    coeffSeq X n m (constLM X A * P) j = A * coeffSeq X n m P j := by
  funext a c
  show ((constLM X A * P) a c).coeff ((j:ℤ) - (m:ℤ)) = (A * coeffSeq X n m P j) a c
  rw [coeff_constLM_mul_lp, Matrix.mul_apply]
  rfl

/-- The coefficient sequence of `P * constLM B` is that of `P` times `B`. -/
lemma coeffSeq_const_mul_bc (n m : ℕ) (B : Matrix (Fin n) (Fin n) C(X,ℂ))
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X,ℂ))) (j : Fin (2*m+1)) :
    coeffSeq X n m (P * constLM X B) j = coeffSeq X n m P j * B := by
  funext a c
  show ((P * constLM X B) a c).coeff ((j:ℤ) - (m:ℤ)) = (coeffSeq X n m P j * B) a c
  rw [coeff_mul_constLM_lp, Matrix.mul_apply]
  rfl

/-- The inverse of a constant unit, as a constant Laurent matrix. -/
lemma constLU_inv_coe_bc (n : ℕ) (M : (Matrix (Fin n) (Fin n) C(X,ℂ))ˣ) :
    (↑(constLU X M)⁻¹ : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X,ℂ)))
      = constLM X (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X,ℂ)) := by
  simp [constLU]

end Coeff

/-! ## Transport to the `Fin ((d+1)*n)`-indexed matrices -/

section Transport

variable (X : Type) [TopologicalSpace X]

lemma blockLastF_eq_bc (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X,ℂ)) :
    blockLastF X n d M = (Matrix.reindexRingEquiv (C(X,ℂ))
      (finProdFinEquiv : Fin (d + 1) × Fin n ≃ Fin ((d + 1) * n))) (blockLast X n d M) := rfl

lemma blockAllF_eq_bc (n d : ℕ) (M : Matrix (Fin n) (Fin n) C(X,ℂ)) :
    blockAllF X n d M = (Matrix.reindexRingEquiv (C(X,ℂ))
      (finProdFinEquiv : Fin (d + 1) × Fin n ≃ Fin ((d + 1) * n))) (blockAll X n d M) := rfl

lemma linAf_eq_bc (n m : ℕ) :
    linAf X n m = (Matrix.reindexRingEquiv (C(X,ℂ))
      (finProdFinEquiv : Fin (2 * m + 1) × Fin n ≃ Fin ((2 * m + 1) * n)))
        (wPenA X n (2 * m)) := rfl

lemma linBf_eq_bc (n m : ℕ) (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X,ℂ))) :
    linBf X n m P = (Matrix.reindexRingEquiv (C(X,ℂ))
      (finProdFinEquiv : Fin (2 * m + 1) × Fin n ≃ Fin ((2 * m + 1) * n)))
        (wPenB X n (2 * m) (coeffSeq X n m P)) := rfl

end Transport

/-! ## The main statement -/

theorem linBf_const_identities_bc (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) :
    (blockLastF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) * linAf X n m = linAf X n m) ∧
    (blockLastF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) * linBf X n m P
      = linBf X n m ((constLU X M : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) * P)) ∧
    (blockAllF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) * linAf X n m
        * blockAllF X n (2 * m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ)) = linAf X n m) ∧
    (blockAllF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) * linBf X n m P
        * blockAllF X n (2 * m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
      = linBf X n m ((constLU X M : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) * P
          * (↑(constLU X M)⁻¹ : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))))) ∧
    (IsUnit (blockLastF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ)))) ∧
    (IsUnit (blockAllF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [blockLastF_eq_bc X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X,ℂ)),
      linAf_eq_bc X n m, ← map_mul,
      blockLast_mul_wPenA_bc X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X,ℂ))]
  · rw [blockLastF_eq_bc X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X,ℂ)),
      linBf_eq_bc X n m P, ← map_mul,
      blockLast_mul_wPenB_bc X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X,ℂ)) (coeffSeq X n m P)]
    have hc : (fun j => (↑M : Matrix (Fin n) (Fin n) C(X,ℂ)) * coeffSeq X n m P j)
        = coeffSeq X n m ((constLU X M : Matrix (Fin n) (Fin n)
            (LaurentPolynomial C(X,ℂ))) * P) := by
      funext j
      rw [constLU_coe, coeffSeq_mul_const_bc X]
    rw [hc]
    rfl
  · rw [blockAllF_eq_bc X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X,ℂ)),
      blockAllF_eq_bc X n (2 * m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X,ℂ)),
      linAf_eq_bc X n m, ← map_mul, ← map_mul,
      blockAll_conj_wPenA_bc X n (2 * m) (↑M) (↑M⁻¹) (Units.mul_inv M)]
  · rw [blockAllF_eq_bc X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X,ℂ)),
      blockAllF_eq_bc X n (2 * m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X,ℂ)),
      linBf_eq_bc X n m P, ← map_mul, ← map_mul,
      blockAll_conj_wPenB_bc X n (2 * m) (↑M) (↑M⁻¹) (Units.mul_inv M) (coeffSeq X n m P)]
    have hc : (fun j => (↑M : Matrix (Fin n) (Fin n) C(X,ℂ)) * coeffSeq X n m P j
            * (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X,ℂ)))
        = coeffSeq X n m ((constLU X M : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X,ℂ))) * P
            * (↑(constLU X M)⁻¹ : Matrix (Fin n) (Fin n)
                (LaurentPolynomial C(X,ℂ)))) := by
      funext j
      rw [constLU_inv_coe_bc X, constLU_coe, coeffSeq_const_mul_bc X, coeffSeq_mul_const_bc X]
    rw [hc]
    rfl
  · rw [blockLastF_eq_bc X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X,ℂ))]
    exact (isUnit_blockLast_bc X n (2 * m) M).map (Matrix.reindexRingEquiv (C(X,ℂ))
      (finProdFinEquiv : Fin (2 * m + 1) × Fin n ≃ Fin ((2 * m + 1) * n)))
  · rw [blockAllF_eq_bc X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X,ℂ))]
    exact (isUnit_blockAll_bc X n (2 * m) M).map (Matrix.reindexRingEquiv (C(X,ℂ))
      (finProdFinEquiv : Fin (2 * m + 1) × Fin n ≃ Fin ((2 * m + 1) * n)))

import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.Linsample
import Submission.Work.KT.Fund.Laurent

/-!
# `Work.KT.FP.LindDefs` — the `3 × 3` blocks of the W linearisation of `(1 - P) + z·P`

The linearisation `z • wPenA + wPenB` of the coefficient sequence `(0, 1 - P, P)` — that is, of
the polynomial `z·((1 - P) + z·P)` — is a `3 × 3` block matrix over `C(X, ℂ)`.  This file fixes the
block notation used by `Work.KT.FP.lind_linear`:

* `lindSig X n P = (0, 1 - P, P)` — the coefficient sequence;
* `lindA`, `lindB` — the `z`-coefficient and the constant coefficient of the pencil, as `3 × 3`
  matrices of `n × n` blocks (so that `blockMat (lindA)` is `wPenA X n 2` and
  `blockMat (lindB X n P)` is `wPenB X n 2 (lindSig X n P)`, see `wPenA_two`, `wPenB_two`);
* `lindC`, `lindD`, `lindE` — the three blocks of the *inverse* of the pencil:

  `(z·A + B)⁻¹·A = z⁻¹·C + z⁻²·D + E`

  with `C = diag(1, P, 0)` (the spectral projection of the pencil), `D` the `(0,1)`-block `P` and
  `E` the `(2,1)`-block `-(1 - P)`.  This is the identity proved in
  `Work.KT.FP.lind_block_identity`;
* `blockMat` — the `3 × 3` blocks read as a matrix on the product index `Fin 3 × Fin n`.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X]

/-! ## The block matrices -/

/-- The coefficient sequence `(0, 1 - P, P)` of the linearisation of `(1 - P) + z·P`. -/
def lindSig (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Fin 3 → Matrix (Fin n) (Fin n) C(X, ℂ) :=
  fun j => if (j : ℕ) = 0 then 0 else if (j : ℕ) = 1 then 1 - P else P

/-- The `z`-coefficient of the W linearisation at `d = 2` (the identity in all blocks but the
last). -/
def lindA (n : ℕ) : Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ)) :=
  fun i j => if i = j ∧ (i : ℕ) ≠ 2 then 1 else 0

/-- The constant coefficient of the W linearisation at `d = 2` for the sequence `(0, 1-P, P)`. -/
def lindB (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ)) :=
  fun i j => if (i : ℕ) + 1 = (j : ℕ) then
      (if (i : ℕ) = 2 then lindSig X n P j else -1)
    else if (i : ℕ) = 2 then lindSig X n P j else 0

/-- The `z⁻¹`-block of `(z·A + B)⁻¹·A`: the projection `diag(1, P, 0)`. -/
def lindC (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ)) :=
  fun i j => if i = j then (if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then P else 0) else 0

/-- The `z⁻²`-block of `(z·A + B)⁻¹·A`: `P` in the `(0,1)`-block. -/
def lindD (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ)) :=
  fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then P else 0

/-- The constant block of `(z·A + B)⁻¹·A`: `-(1 - P)` in the `(2,1)`-block. -/
def lindE (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ)) :=
  fun i j => if (i : ℕ) = 2 ∧ (j : ℕ) = 1 then -(1 - P) else 0

/-- A `3 × 3` matrix of `n × n` blocks, read as a matrix on the product index `Fin 3 × Fin n`. -/
abbrev blockMat (n : ℕ) (M : Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ))) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) C(X, ℂ) :=
  fun i j => M i.1 j.1 i.2 j.2

/-! ## Reading the blocks as a matrix -/

@[simp] lemma blockMat_apply (n : ℕ)
    (M : Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ)))
    (i j : Fin 3 × Fin n) : blockMat X n M i j = M i.1 j.1 i.2 j.2 := rfl

/-- Block multiplication: the product of the `blockMat`s is the `blockMat` of the product. -/
lemma blockMat_mul (n : ℕ) (M N : Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ))) :
    blockMat X n (M * N) = blockMat X n M * blockMat X n N := by
  ext ⟨i, a⟩ ⟨j, b⟩ x
  simp only [blockMat, Matrix.mul_apply, Matrix.sum_apply, ContinuousMap.sum_apply,
    Fintype.sum_prod_type]

lemma blockMat_add (n : ℕ) (M N : Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ))) :
    blockMat X n (M + N) = blockMat X n M + blockMat X n N := by
  ext i j
  simp [blockMat]

lemma blockMat_zero (n : ℕ) :
    blockMat X n (0 : Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ))) = 0 := by
  ext i j
  simp [blockMat]

lemma blockMat_neg (n : ℕ) (M : Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ))) :
    blockMat X n (-M) = -blockMat X n M := by
  ext i j
  simp [blockMat]

lemma blockMat_sub (n : ℕ) (M N : Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ))) :
    blockMat X n (M - N) = blockMat X n M - blockMat X n N := by
  ext i j
  simp [blockMat]

lemma blockMat_smul (n : ℕ) (c : ℂ)
    (M : Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ))) :
    blockMat X n (c • M) = c • blockMat X n M := by
  ext i j
  simp [blockMat]

/-! ## Reindexing -/

section Reindex

variable {A : Type} {m m' : Type} [Fintype m] [Fintype m']

lemma reindexMat_add [Add A] (e : m ≃ m') (M N : Matrix m m A) :
    Matrix.reindex e e (M + N) = Matrix.reindex e e M + Matrix.reindex e e N := by
  ext i j; simp [Matrix.reindex_apply]

lemma reindexMat_sub [Sub A] (e : m ≃ m') (M N : Matrix m m A) :
    Matrix.reindex e e (M - N) = Matrix.reindex e e M - Matrix.reindex e e N := by
  ext i j; simp [Matrix.reindex_apply]

lemma reindexMat_neg [Neg A] (e : m ≃ m') (M : Matrix m m A) :
    Matrix.reindex e e (-M) = -Matrix.reindex e e M := by
  ext i j; simp [Matrix.reindex_apply]

lemma reindexMat_zero [Zero A] (e : m ≃ m') :
    Matrix.reindex e e (0 : Matrix m m A) = 0 := by
  ext i j; simp [Matrix.reindex_apply]

lemma reindexMat_smul {R : Type} [SMul R A] (e : m ≃ m') (c : R) (M : Matrix m m A) :
    Matrix.reindex e e (c • M) = c • Matrix.reindex e e M := by
  ext i j; simp [Matrix.reindex_apply]

lemma reindexMat_mul [AddCommMonoid A] [Mul A] (e : m ≃ m') (M N : Matrix m m A) :
    Matrix.reindex e e M * Matrix.reindex e e N = Matrix.reindex e e (M * N) :=
  Work.KT.reindexMul e e e M N

end Reindex

/-! ## The coefficient sequence and the bridges to `wPenA`/`wPenB` -/

/-- Coefficient of `single 0 x + single 1 y` (i.e. of `C x + C y·T`) at `k`. -/
lemma coeff_single_zero_add_single_one {A : Type} [Semiring A] (x y : A) (k : ℤ) :
    (((AddMonoidAlgebra.single (0 : ℤ) x + AddMonoidAlgebra.single (1 : ℤ) y) :
        LaurentPolynomial A).coeff) k
      = (if (0 : ℤ) = k then x else 0) + (if (1 : ℤ) = k then y else 0) := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_single_apply,
    AddMonoidAlgebra.coeff_single_apply]

/-- Coefficient of `C x + C y·T` at `k`. -/
lemma coeff_C_add_C_mul_T {A : Type} [Semiring A] (x y : A) (k : ℤ) :
    ((LaurentPolynomial.C x + LaurentPolynomial.C y * LaurentPolynomial.T 1 :
        LaurentPolynomial A).coeff) k
      = (if (0 : ℤ) = k then x else 0) + (if (1 : ℤ) = k then y else 0) := by
  rw [← LaurentPolynomial.single_eq_C_mul_T y 1,
    show (LaurentPolynomial.C x : LaurentPolynomial A) = AddMonoidAlgebra.single (0 : ℤ) x from by
      rw [LaurentPolynomial.single_eq_C_mul_T]; simp,
    coeff_single_zero_add_single_one]

/-- The coefficient sequence of `linSample X n P` is `(0, 1 - P, P)`. -/
lemma coeffSeq_linSample (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    coeffSeq X n 1 (linSample X n P) = lindSig X n P := by
  funext j a c
  ext x
  fin_cases j <;>
    simp only [coeffSeq, linSample, lindSig, coeff_C_add_C_mul_T] <;>
    norm_num

/-- `blockMat (lindA)` is `wPenA X n 2`. -/
lemma wPenA_two (n : ℕ) : wPenA X n 2 = blockMat X n (lindA X n) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [wPenA, lindA, blockMat, Matrix.ite_apply]
  by_cases h : i = j ∧ (i : ℕ) ≠ 2 <;> simp [h]

/-- `blockMat (lindB)` is `wPenB X n 2 (lindSig)`. -/
lemma wPenB_two (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    wPenB X n 2 (lindSig X n P) = blockMat X n (lindB X n P) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [wPenB, lindB, blockMat, lindSig, Matrix.ite_apply]
  split_ifs <;> rfl

/-- The `z`-coefficient of the linearisation of `linSample X n P`. -/
lemma linAf_eq (n : ℕ) :
    linAf X n 1 = Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindA X n)) := by
  rw [show linAf X n 1
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (wPenA X n 2) from rfl,
    wPenA_two]

/-- The constant coefficient of the linearisation of `linSample X n P`. -/
lemma linBf_eq (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    linBf X n 1 (linSample X n P)
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindB X n P)) := by
  rw [show linBf X n 1 (linSample X n P)
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          (wPenB X n 2 (coeffSeq X n 1 (linSample X n P))) from rfl,
    coeffSeq_linSample, wPenB_two]

/-- `lindC` is an idempotent matrix of blocks. -/
lemma lindC_idem (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    lindC X n P * lindC X n P = lindC X n P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lindC, Matrix.mul_apply, hP]

end

end Work.KT.FP

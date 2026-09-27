import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Laurent
import Submission.Work.KT.Fund.kappa_add

/-!
# `Work.KT.FP.FpDefs` — shared definitions for the `fund_product` split

This file fixes the notation used by the `fp_inj` node (Bott injectivity) of the split of
`Work.KT.fund_product`.

* `bottUnit X n P hP` is the **Bott unit** `(1 - P) + z·P` of an idempotent `P` over `C(X, ℂ)`,
  an invertible matrix over `C(X × S¹, ℂ)` (its inverse is `z⁻¹·P + (1 - P)`);
* `padUnit X k u` is the **padded unit** `u ⊕ 1_k`, on the index set `Fin (n + k)`;
* `pM X M` is the pull-back of a matrix over `C(X, ℂ)` to `X × S¹` (equal to
  `Work.KT.Fund.pullMat X M`), together with the elementary lemmas recording that it commutes
  with `+`, `-`, `*`, `0`, `1`.

Nothing here is mathematically deep; it exists so that the statements of the sibling nodes
(`Work.KT.FP.kappa_bott`, `Work.KT.FP.kappa_eq_disc`, `Work.KT.FP.bott_index`) can be written
without repeating the same matrix bookkeeping.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## The pull-back of matrices to `X × S¹` -/

/-- The ring hom `C(X, ℂ) → C(X × S¹, ℂ)` pulling back along the projection. -/
def pMRH : C(X, ℂ) →+* C(X × Sph ℂ, ℂ) :=
  (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom

/-- The entrywise pull-back of a matrix over `C(X, ℂ)` to `X × S¹`.  Equal to
`Work.KT.Fund.pullMat X M` (`pullMat_eq_pM`). -/
def pM {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  M.map ⇑(pMRH X)

lemma pullMat_eq_pM {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Fund.pullMat X M = pM X M := rfl

@[simp] lemma pM_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n)
    (p : X × Sph ℂ) : pM X M i j p = M i j p.1 := rfl

lemma pM_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    pM X (A * B) = pM X A * pM X B :=
  (Work.KT.Matrix.map_mul' (pMRH X) A B).symm

lemma pM_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    pM X (A + B) = pM X A + pM X B :=
  Matrix.map_add (⇑(pMRH X)) (fun a b => map_add (pMRH X) a b) A B

lemma pM_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    pM X (A - B) = pM X A - pM X B :=
  Matrix.map_sub (⇑(pMRH X)) (fun a b => map_sub (pMRH X) a b) A B

lemma pM_zero {n : ℕ} : pM X (0 : Matrix (Fin n) (Fin n) C(X, ℂ)) = 0 :=
  Matrix.map_zero _ (map_zero (pMRH X))

lemma pM_one {n : ℕ} : pM X (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) = 1 :=
  Matrix.map_one _ (map_zero (pMRH X)) (map_one (pMRH X))

lemma pM_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    pM X (-A) = -pM X A :=
  Matrix.map_neg _ (fun a => map_neg (pMRH X) a) A

/-! ## The Bott unit of an idempotent -/

/-- The clutching matrix `(1 - P) + z·P` of the Bott unit of an idempotent `P`. -/
def bottMat {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  pM X (1 - P) + (zUnit X : C(X × Sph ℂ, ℂ)) • pM X P

/-- The inverse matrix `z⁻¹·P + (1 - P)` of `bottMat X P`. -/
def bottMatInv {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) • pM X P + pM X (1 - P)

/-- The algebraic identity behind `bottMat * bottMatInv = 1`: orthogonal idempotents `A`, `B`
summing to `1` give `(A + zB)(z⁻¹B + A) = 1`. -/
lemma bott_mul_generic {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (z : Rˣ)
    (hAA : A * A = A) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = B) (hsum : A + B = 1) :
    (A + (z : R) • B) * ((↑(z⁻¹) : R) • B + A) = 1 := by
  have h1 : A * ((↑(z⁻¹) : R) • B) = 0 := by rw [Matrix.mul_smul, hAB, smul_zero]
  have h2 : ((z : R) • B) * ((↑(z⁻¹) : R) • B) = B := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul, hBB]
  have h4 : ((z : R) • B) * A = 0 := by rw [Matrix.smul_mul, hBA, smul_zero]
  calc (A + (z : R) • B) * ((↑(z⁻¹) : R) • B + A)
      = (A + (z : R) • B) * ((↑(z⁻¹) : R) • B) + (A + (z : R) • B) * A := by
        rw [Matrix.mul_add]
    _ = (A * ((↑(z⁻¹) : R) • B) + ((z : R) • B) * ((↑(z⁻¹) : R) • B))
          + (A * A + ((z : R) • B) * A) := by rw [Matrix.add_mul, Matrix.add_mul]
    _ = 0 + B + (A + 0) := by rw [h1, h2, hAA, h4]
    _ = 1 := by rw [zero_add, add_zero, add_comm, hsum]

/-- The reverse product identity: `(z⁻¹B + A)(A + zB) = 1`. -/
lemma bott_mul_generic' {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (z : Rˣ)
    (hAA : A * A = A) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = B) (hsum : A + B = 1) :
    ((↑(z⁻¹) : R) • B + A) * (A + (z : R) • B) = 1 := by
  have h1 : ((↑(z⁻¹) : R) • B) * A = 0 := by rw [Matrix.smul_mul, hBA, smul_zero]
  have h2 : ((↑(z⁻¹) : R) • B) * ((z : R) • B) = B := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul, hBB]
  have h4 : A * ((z : R) • B) = 0 := by rw [Matrix.mul_smul, hAB, smul_zero]
  calc ((↑(z⁻¹) : R) • B + A) * (A + (z : R) • B)
      = ((↑(z⁻¹) : R) • B + A) * A + ((↑(z⁻¹) : R) • B + A) * ((z : R) • B) := by
        rw [Matrix.mul_add]
    _ = (((↑(z⁻¹) : R) • B) * A + A * A)
          + (((↑(z⁻¹) : R) • B) * ((z : R) • B) + A * ((z : R) • B)) := by
        rw [Matrix.add_mul, Matrix.add_mul]
    _ = 0 + A + (B + 0) := by rw [h1, h2, hAA, h4]
    _ = 1 := by rw [zero_add, add_zero, hsum]

lemma base_idem' {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  have h : (1 - P) * (1 - P) = 1 - P - (P - P * P) := by rw [sub_mul, one_mul, mul_sub, mul_one]
  rw [h, hP, sub_self, sub_zero]

lemma base_orth1 {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]

lemma base_orth2 {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]

lemma bottMat_mul_inv {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    bottMat X P * bottMatInv X P = 1 := by
  have hAA : pM X (1 - P) * pM X (1 - P) = pM X (1 - P) := by
    rw [← pM_mul, base_idem' X P hP]
  have hAB : pM X (1 - P) * pM X P = 0 := by rw [← pM_mul, base_orth1 X P hP, pM_zero]
  have hBA : pM X P * pM X (1 - P) = 0 := by rw [← pM_mul, base_orth2 X P hP, pM_zero]
  have hBB : pM X P * pM X P = pM X P := by rw [← pM_mul, hP]
  have hsum : pM X (1 - P) + pM X P = 1 := by
    rw [← pM_add, show (1 - P) + P = 1 from by abel, pM_one]
  rw [bottMat, bottMatInv]
  exact bott_mul_generic (pM X (1 - P)) (pM X P) (zUnit X) hAA hAB hBA hBB hsum

lemma bottMat_inv_mul {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    bottMatInv X P * bottMat X P = 1 := by
  have hAA : pM X (1 - P) * pM X (1 - P) = pM X (1 - P) := by
    rw [← pM_mul, base_idem' X P hP]
  have hAB : pM X (1 - P) * pM X P = 0 := by rw [← pM_mul, base_orth1 X P hP, pM_zero]
  have hBA : pM X P * pM X (1 - P) = 0 := by rw [← pM_mul, base_orth2 X P hP, pM_zero]
  have hBB : pM X P * pM X P = pM X P := by rw [← pM_mul, hP]
  have hsum : pM X (1 - P) + pM X P = 1 := by
    rw [← pM_add, show (1 - P) + P = 1 from by abel, pM_one]
  rw [bottMat, bottMatInv]
  exact bott_mul_generic' (pM X (1 - P)) (pM X P) (zUnit X) hAA hAB hBA hBB hsum

/-- The **Bott unit** `(1 - P) + z·P` of an idempotent `P` over `C(X, ℂ)`. -/
def bottUnit (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ where
  val := bottMat X P
  inv := bottMatInv X P
  val_inv := bottMat_mul_inv X P hP
  inv_val := bottMat_inv_mul X P hP

@[simp] lemma bottUnit_val {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    ((bottUnit X n P hP : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = bottMat X P := rfl

/-- The boundary restriction of a unit over the disc `D` to the circle `S¹` (entrywise, as a
matrix).  The two `g`'s of `Work.KT.FP.kappa_eq_disc`/`bott_index` live in this form. -/
def bdryMat {m : ℕ} (g : (Matrix (Fin m) (Fin m) C(X × Ball ℂ, ℂ))ˣ) :
    Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ) :=
  ((g : Matrix (Fin m) (Fin m) C(X × Ball ℂ, ℂ))).map (⇑(Fund.bdryRestrict X))

@[simp] lemma bdryMat_apply {m : ℕ} (g : (Matrix (Fin m) (Fin m) C(X × Ball ℂ, ℂ))ˣ)
    (i j : Fin m) (p : X × Sph ℂ) :
    bdryMat X g i j p = ((g : Matrix (Fin m) (Fin m) C(X × Ball ℂ, ℂ)) i j)
      ⟨p.1, Fund.sphIncl p.2⟩ := rfl

/-! ## Padding a unit with a trivial summand -/

/-- The unit `u ⊕ 1_k`, on the index set `Fin (n + k)`. -/
def padUnit {n : ℕ} (k : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
      (1 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
      (1 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))
  val_inv := by
    rw [Work.KT.reindexMul, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Units.mul_inv, mul_one]
    rw [Matrix.fromBlocks_one, Work.KT.Fund.reindex_one']
  inv_val := by
    rw [Work.KT.reindexMul, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Units.inv_mul, mul_one]
    rw [Matrix.fromBlocks_one, Work.KT.Fund.reindex_one']

@[simp] lemma padUnit_val {n : ℕ} (k : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    ((padUnit X k u : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
            (1 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))) := rfl

end

end Work.KT.FP

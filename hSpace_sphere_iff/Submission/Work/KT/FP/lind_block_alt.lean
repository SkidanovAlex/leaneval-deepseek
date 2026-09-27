import Mathlib
import Submission.Work.KT.FP.LindDefs

/-!
# `Work.KT.FP.lind_block_alt` — the `3 × 3` block identity of the `d = 2` W linearisation

For an idempotent `P` and `z ≠ 0`,

`(z·A + B)·(z⁻¹·C + z⁻²·D + E) = A`

with `A = lindA = diag(1,1,0)`, `B = lindB`, `C = lindC = diag(1,P,0)`, `D = lindD` (the
`(0,1)`-block `P`) and `E = lindE` (the `(2,1)`-block `-(1-P)`).

The six products of the individual blocks `A·C = C`, `A·D = D`, `A·E = 0`, `B·C = -D`,
`B·D = 0`, `B·E = A - C` are computed entrywise (`Matrix.mul_apply`, `Fin.sum_univ_three`,
`fin_cases`), and the scalar bookkeeping is `Matrix.smul_mul`/`Matrix.mul_smul`/`smul_smul`
with `z·z⁻¹ = 1`.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable (X : Type) [TopologicalSpace X] (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ))

/-! ## The block products -/

lemma lindA_mul_lindC : lindA X n * lindC X n P = lindC X n P := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [lindA, lindC, Matrix.one_apply]

lemma lindA_mul_lindD : lindA X n * lindD X n P = lindD X n P := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [lindA, lindD, Matrix.one_apply]

lemma lindA_mul_lindE : lindA X n * lindE X n P = 0 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [lindA, lindE, Matrix.one_apply]

lemma lindB_mul_lindC (hP : P * P = P) : lindB X n P * lindC X n P = -lindD X n P := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [lindB, lindC, lindD, lindSig, Matrix.one_apply, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hP, sub_self] <;> abel

lemma lindB_mul_lindD (hP : P * P = P) : lindB X n P * lindD X n P = 0 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [lindB, lindD, lindSig, Matrix.one_apply, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hP, sub_self] <;> abel

lemma lindB_mul_lindE (hP : P * P = P) :
    lindB X n P * lindE X n P = lindA X n - lindC X n P := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [lindA, lindB, lindC, lindE, lindSig, Matrix.one_apply, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hP, sub_self] <;> abel

/-! ## The identity -/

/-- `(z·A + B)·(z⁻¹·C + z⁻²·D + E) = A`.

The two compactness hypotheses are not used mathematically; they are what makes instance
resolution pick the right `SMul ℂ (Matrix _ _ C(X, ℂ))` instance for the scalar rewrites
`Matrix.smul_mul`/`Matrix.mul_smul`. -/
theorem lind_block_identity_alt [CompactSpace X] [T2Space X] (hP : P * P = P) {z : ℂ}
    (hz : z ≠ 0) :
    (z • blockMat X n (lindA X n) + blockMat X n (lindB X n P)) *
        (z⁻¹ • blockMat X n (lindC X n P) + (z⁻¹ * z⁻¹) • blockMat X n (lindD X n P)
          + blockMat X n (lindE X n P))
      = blockMat X n (lindA X n) := by
  haveI hT1 : IsScalarTower ℂ (Matrix (Fin n) (Fin n) C(X, ℂ))
      (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.Semiring.isScalarTower
  haveI hT2 : IsScalarTower ℂ (Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ)))
      (Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ))) := Matrix.Semiring.isScalarTower
  haveI hC1 : SMulCommClass ℂ (Matrix (Fin n) (Fin n) C(X, ℂ))
      (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.Semiring.smulCommClass
  haveI hC2 : SMulCommClass ℂ (Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ)))
      (Matrix (Fin 3) (Fin 3) (Matrix (Fin n) (Fin n) C(X, ℂ))) := Matrix.Semiring.smulCommClass
  have e1 : (z • blockMat X n (lindA X n)) * (z⁻¹ • blockMat X n (lindC X n P))
      = blockMat X n (lindA X n) * blockMat X n (lindC X n P) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]
  have e2 : (z • blockMat X n (lindA X n)) * ((z⁻¹ * z⁻¹) • blockMat X n (lindD X n P))
      = z⁻¹ • (blockMat X n (lindA X n) * blockMat X n (lindD X n P)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  have e3 : (z • blockMat X n (lindA X n)) * blockMat X n (lindE X n P)
      = z • (blockMat X n (lindA X n) * blockMat X n (lindE X n P)) := by
    rw [Matrix.smul_mul]
  have e4 : blockMat X n (lindB X n P) * (z⁻¹ • blockMat X n (lindC X n P))
      = z⁻¹ • (blockMat X n (lindB X n P) * blockMat X n (lindC X n P)) := by
    rw [Matrix.mul_smul]
  have e5 : blockMat X n (lindB X n P) * ((z⁻¹ * z⁻¹) • blockMat X n (lindD X n P))
      = (z⁻¹ * z⁻¹) • (blockMat X n (lindB X n P) * blockMat X n (lindD X n P)) := by
    rw [Matrix.mul_smul]
  have b1 : blockMat X n (lindA X n) * blockMat X n (lindC X n P)
      = blockMat X n (lindC X n P) := by
    rw [← blockMat_mul, lindA_mul_lindC X n P]
  have b2 : blockMat X n (lindA X n) * blockMat X n (lindD X n P)
      = blockMat X n (lindD X n P) := by
    rw [← blockMat_mul, lindA_mul_lindD X n P]
  have b3 : blockMat X n (lindA X n) * blockMat X n (lindE X n P) = 0 := by
    rw [← blockMat_mul, lindA_mul_lindE X n P, blockMat_zero]
  have b4 : blockMat X n (lindB X n P) * blockMat X n (lindC X n P)
      = -blockMat X n (lindD X n P) := by
    rw [← blockMat_mul, lindB_mul_lindC X n P hP, blockMat_neg]
  have b5 : blockMat X n (lindB X n P) * blockMat X n (lindD X n P) = 0 := by
    rw [← blockMat_mul, lindB_mul_lindD X n P hP, blockMat_zero]
  have b6 : blockMat X n (lindB X n P) * blockMat X n (lindE X n P)
      = blockMat X n (lindA X n) - blockMat X n (lindC X n P) := by
    rw [← blockMat_mul, lindB_mul_lindE X n P hP, blockMat_sub]
  simp only [mul_add, add_mul]
  rw [e1, e2, e3, e4, e5, b1, b2, b3, b4, b5, b6, smul_zero, smul_zero, smul_neg]
  abel

end

end Work.KT.FP

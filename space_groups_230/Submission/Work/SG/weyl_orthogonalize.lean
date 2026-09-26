import Mathlib
import Submission.Work.SG.weyl_conj_sum_invariant
import Submission.Work.SG.weyl_sum_transpose_mul_posDef

/-!
# Weyl's unitarization trick for a finite group of invertible matrices

Given a finite set `P` of invertible real matrices containing `1` and closed under
multiplication (so `P` is a finite group of matrices), the "averaged Gram matrix"

`S = ∑ A ∈ P, Aᵀ * A`

is symmetric and positive definite, and `P` is invariant under the conjugation action of
its elements: `Aᵀ * S * A = S` for every `A ∈ P` (see `weyl_conj_sum_invariant`).

Taking `M = CFC.sqrt S` (the symmetric positive-definite square root of `S`, which in
Mathlib is the continuous functional calculus square root), we get a symmetric `M` with
`M * M = S` and `0 < M.det`. For every `A ∈ P`,

`(M A M⁻¹)ᵀ (M A M⁻¹) = M⁻¹ Aᵀ (M M) A M⁻¹ = M⁻¹ (Aᵀ S A) M⁻¹ = M⁻¹ S M⁻¹ = 1`,

i.e. every element of `P` becomes orthogonal after conjugation by `M`. This is the lemma
used to put a crystallographic point group into a canonical orthogonal form.
-/

namespace Work.SG

open Matrix
open scoped MatrixOrder

theorem weyl_orthogonalize {n : Type*} [Fintype n] [DecidableEq n]
    (P : Finset (Matrix n n ℝ)) (h1 : (1 : Matrix n n ℝ) ∈ P)
    (hmul : ∀ A ∈ P, ∀ B ∈ P, A * B ∈ P) (hunit : ∀ A ∈ P, A.det ≠ 0) :
    ∃ M : Matrix n n ℝ, Matrix.transpose M = M ∧
      M * M = ∑ A ∈ P, Matrix.transpose A * A ∧ 0 < M.det ∧
      ∀ A ∈ P, Matrix.transpose (M * A * M⁻¹) * (M * A * M⁻¹) = 1 := by
  classical
  -- The averaged Gram matrix `S = ∑ A, Aᵀ * A`.
  set S : Matrix n n ℝ := ∑ A ∈ P, Matrix.transpose A * A with hSdef
  -- `S` is positive definite, because `1 ∈ P` contributes the identity.
  have hPosDef : S.PosDef := by
    rw [hSdef]
    exact weyl_sum_transpose_mul_posDef P h1
  have hpsd : S.PosSemidef := hPosDef.posSemidef
  have hnonneg : (0 : Matrix n n ℝ) ≤ S := hpsd.nonneg
  -- `M := CFC.sqrt S` is symmetric.
  have hsymm : Matrix.transpose (CFC.sqrt S) = CFC.sqrt S := by
    have h : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
      (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian.eq
    have hct : (CFC.sqrt S)ᴴ = Matrix.transpose (CFC.sqrt S) := by
      ext i j; simp [Matrix.conjTranspose]
    exact hct ▸ h
  -- `M * M = S`.
  have hsq : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hnonneg
  -- `0 < S.det` and hence `0 < M.det`.
  have hdetS : 0 < S.det := by
    rw [hSdef]; exact hPosDef.det_pos
  have hdetpos : 0 < (CFC.sqrt S).det := by
    rw [PosSemidef.det_sqrt hpsd]
    simp only [RCLike.sqrt_real]
    exact Real.sqrt_pos.mpr hdetS
  refine ⟨CFC.sqrt S, hsymm, ?_, hdetpos, ?_⟩
  · rw [hsq, hSdef]
  · -- Conjugation by `M` sends each `A ∈ P` to an orthogonal matrix.
    intro A hA
    -- `M` is invertible.
    have hMinv : IsUnit (CFC.sqrt S).det := isUnit_iff_ne_zero.mpr (ne_of_gt hdetpos)
    have h1' : CFC.sqrt S * (CFC.sqrt S)⁻¹ = 1 := by
      simpa using Matrix.mul_nonsing_inv_cancel_right (CFC.sqrt S) (1 : Matrix n n ℝ) hMinv
    have h2' : (CFC.sqrt S)⁻¹ * CFC.sqrt S = 1 := by
      simpa using Matrix.nonsing_inv_mul_cancel_right (CFC.sqrt S) (1 : Matrix n n ℝ) hMinv
    have hMT : Matrix.transpose ((CFC.sqrt S)⁻¹) = (CFC.sqrt S)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hsymm]
    -- Invariance of `S` under `A`.
    have hinv : Matrix.transpose A * S * A = S := by
      rw [hSdef]; exact weyl_conj_sum_invariant P hmul hunit A hA
    have step1 : Matrix.transpose (CFC.sqrt S * A * (CFC.sqrt S)⁻¹) *
          (CFC.sqrt S * A * (CFC.sqrt S)⁻¹)
        = (CFC.sqrt S)⁻¹ * (Matrix.transpose A * (CFC.sqrt S * CFC.sqrt S) * A) *
            (CFC.sqrt S)⁻¹ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hMT, hsymm]
      noncomm_ring
    have h3 : (CFC.sqrt S)⁻¹ * S * (CFC.sqrt S)⁻¹ = 1 := by
      calc (CFC.sqrt S)⁻¹ * S * (CFC.sqrt S)⁻¹
          = (CFC.sqrt S)⁻¹ * (CFC.sqrt S * CFC.sqrt S) * (CFC.sqrt S)⁻¹ := by rw [hsq]
        _ = 1 := by rw [← mul_assoc, h2', one_mul, h1']
    rw [step1, hsq, hinv]
    exact h3

end Work.SG

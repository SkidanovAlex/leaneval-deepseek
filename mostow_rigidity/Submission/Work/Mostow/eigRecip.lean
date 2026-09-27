import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.poAux

/-!
# Eigenvalues of an element of `O(n,1)` occur in reciprocal pairs

An element `A` of `O(n,1)` preserves the Minkowski form with matrix `J = diag(1,…,1,−1)`,
i.e. `Aᵀ J A = J`, whence `Aᵀ = J A⁻¹ J` is conjugate to `A⁻¹`.  Consequently the
characteristic polynomials of `A` and of `A⁻¹` coincide, and every real eigenvalue of `A`
has reciprocal also an eigenvalue.  This is the linear-algebra input used to replace a
level-scaling (loxodromic) direction of a `PO(n,1)`-element by its inverse.

The proof below avoids matrices inverses: from `A v = lam • v` and `Aᵀ J A = J` one gets
`Aᵀ (J v) = lam⁻¹ (J v)`, so `lam⁻¹` is an eigenvalue of `Aᵀ`; since `A` and `Aᵀ` have the
same characteristic polynomial, `det (lam⁻¹ • 1 - A) = 0`, and a non-zero vector in the
kernel is the required eigenvector of `A`.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-- `M.charpoly.eval t = det (t • 1 - M)`. -/
private lemma charpoly_eval_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (t : ℝ) : M.charpoly.eval t = (t • 1 - M).det := by
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

/-- If `v ≠ 0` is an eigenvector of `M` for the eigenvalue `lam` and `Mᵀ J M = J` with
`J = diag(1,…,1,−1)`, then `lam⁻¹` is also an eigenvalue of `M`. -/
private lemma exists_eigen_recip (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hJ : Mᵀ * pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) * M
      = pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ))
    (lam : ℝ) (h : ∃ v : Fin n ⊕ Fin 1 → ℝ, v ≠ 0 ∧ M *ᵥ v = lam • v) :
    ∃ w : Fin n ⊕ Fin 1 → ℝ, w ≠ 0 ∧ M *ᵥ w = lam⁻¹ • w := by
  obtain ⟨v, hv, hvev⟩ := h
  set J : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
    pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef]
    exact pmOneMat_mul_pmOneMat (Fin n) (Fin 1) ℝ
  have hJ' : Mᵀ * J * M = J := by
    rw [hJdef]
    exact hJ
  -- `J v ≠ 0`
  have hx : J *ᵥ v ≠ 0 := by
    intro hz
    have h2 : v = 0 := by
      have h3 : J *ᵥ (J *ᵥ v) = 0 := by rw [hz, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec] at h3
    exact hv h2
  -- the key relation `lam • (Mᵀ (J v)) = J v`
  have hrel : lam • (Mᵀ *ᵥ (J *ᵥ v)) = J *ᵥ v := by
    have h4 : (Mᵀ * J * M) *ᵥ v = J *ᵥ v := by rw [hJ']
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h4
    simp only [hvev, Matrix.mulVec_smul] at h4
    exact h4
  have hlam : lam ≠ 0 := by
    intro h0
    refine hx ?_
    rw [← hrel, h0, zero_smul]
  -- `lam⁻¹` is an eigenvalue of `Mᵀ`
  have htrans : Mᵀ *ᵥ (J *ᵥ v) = lam⁻¹ • (J *ᵥ v) := by
    have h5 := congrArg (fun z : Fin n ⊕ Fin 1 → ℝ => lam⁻¹ • z) hrel
    simpa only [smul_smul, inv_mul_cancel₀ hlam, one_smul] using h5
  have hker : (lam⁻¹ • 1 - Mᵀ) *ᵥ (J *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, htrans, sub_self]
  have hdetT : (lam⁻¹ • 1 - Mᵀ).det = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff (M := lam⁻¹ • 1 - Mᵀ)).mp ⟨J *ᵥ v, hx, hker⟩
  -- transfer to `M` via equality of characteristic polynomials
  have hdet : (lam⁻¹ • 1 - M).det = 0 := by
    have hh := hdetT
    rw [← charpoly_eval_eq_det Mᵀ lam⁻¹, Matrix.charpoly_transpose M,
      charpoly_eval_eq_det M lam⁻¹] at hh
    exact hh
  obtain ⟨w, hw, hw0⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := lam⁻¹ • 1 - M)).mpr hdet
  refine ⟨w, hw, ?_⟩
  have hsub : lam⁻¹ • w - M *ᵥ w = 0 := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hw0
  exact (sub_eq_zero.mp hsub).symm

theorem eigRecip (n : ℕ) (A : O1 n) (lam : ℝ)
    (h : ∃ v : Fin n ⊕ Fin 1 → ℝ, v ≠ 0 ∧ Matrix.mulVec (mat A) v = lam • v) :
    ∃ w : Fin n ⊕ Fin 1 → ℝ, w ≠ 0 ∧ Matrix.mulVec (mat A) w = lam⁻¹ • w :=
  exists_eigen_recip (mat A) (O1_form_col A) lam h

end

end Work.Mostow

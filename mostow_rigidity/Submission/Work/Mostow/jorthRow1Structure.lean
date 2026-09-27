import Mathlib
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.poAux

/-!
# The structure of the row/column `Sum.inl 1` of a `J`-orthogonal `3 × 3` matrix

Let `A : O(2,1)`, so that `M = mat A` satisfies `M J Mᵀ = J` with `J = pmOneMat = diag(1,1,-1)`.
If the row of `M` with index `Sum.inl 1` vanishes off the diagonal, then so does the column with
index `Sum.inl 1`, and the diagonal entry is `±1`.

The proof is the elementary computation

* `Mᵀ *ᵥ e = c • e` (row hypothesis, `c = M (inl 1) (inl 1)`, `e = Pi.single (inl 1) 1`),
* `(M J Mᵀ) *ᵥ e = J *ᵥ e = e` gives `c • (M *ᵥ e) = e`,
* the `inl 1` entry of the latter gives `c * c = 1`, hence `M *ᵥ e = c • e`,
* reading the three entries of `M *ᵥ e = c • e` gives the claim.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open Matrix

noncomputable section

/-- The basis vector of `ℝ^{Fin 2 ⊕ Fin 1}` supported at `Sum.inl 1`. -/
def jE : Fin 2 ⊕ Fin 1 → ℝ := Pi.single (Sum.inl 1) (1 : ℝ)

@[simp] lemma jE_inl_one : jE (Sum.inl 1) = 1 := by simp [jE]

@[simp] lemma jE_inl_zero : jE (Sum.inl 0) = 0 := by simp [jE]

@[simp] lemma jE_inr_zero : jE (Sum.inr 0) = 0 := by simp [jE]

lemma mulVec_jE (M : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) :
    M *ᵥ jE = M.col (Sum.inl 1) := by
  rw [jE, Matrix.mulVec_single_one]

lemma mulVec_jE_apply (M : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) (i : Fin 2 ⊕ Fin 1) :
    (M *ᵥ jE) i = M i (Sum.inl 1) := by
  rw [mulVec_jE, Matrix.col_apply]

lemma pmOneMat_mulVec_jE :
    (pmOneMat (p := Fin 2) (q := Fin 1) (α := ℝ)) *ᵥ jE = jE := by
  rw [jE, Submission.Mostow.Hyper.pmOneMat_mulVec]
  funext k
  rcases k with i | i
  · fin_cases i <;> simp
  · fin_cases i <;> simp

theorem jorthRow1Structure (A : Submission.Mostow.O1 2)
    (h10 : Submission.Mostow.mat A (Sum.inl 1) (Sum.inl 0) = 0)
    (h12 : Submission.Mostow.mat A (Sum.inl 1) (Sum.inr 0) = 0) :
    Submission.Mostow.mat A (Sum.inl 0) (Sum.inl 1) = 0 ∧
    Submission.Mostow.mat A (Sum.inr 0) (Sum.inl 1) = 0 ∧
    (Submission.Mostow.mat A (Sum.inl 1) (Sum.inl 1) = 1 ∨
      Submission.Mostow.mat A (Sum.inl 1) (Sum.inl 1) = -1) := by
  set M : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ := Submission.Mostow.mat A with hM
  set c : ℝ := M (Sum.inl 1) (Sum.inl 1) with hc
  have h10' : M (Sum.inl 1) (Sum.inl 0) = 0 := by rw [hM]; exact h10
  have h12' : M (Sum.inl 1) (Sum.inr 0) = 0 := by rw [hM]; exact h12
  have hform : M * (pmOneMat (p := Fin 2) (q := Fin 1) (α := ℝ)) * Mᵀ = pmOneMat := by
    rw [hM]; exact O1_form_row A
  -- the row hypothesis, as a vector equation
  have hrow : Mᵀ *ᵥ jE = c • jE := by
    rw [mulVec_jE]
    funext i
    rw [Matrix.col_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
    rcases i with i | i
    · fin_cases i <;> simp_all
    · fin_cases i <;> simp_all
  -- the form relation applied to the basis vector
  have hcol : c • (M *ᵥ jE) = jE := by
    have h : (M * (pmOneMat (p := Fin 2) (q := Fin 1) (α := ℝ)) * Mᵀ) *ᵥ jE
        = (pmOneMat (p := Fin 2) (q := Fin 1) (α := ℝ)) *ᵥ jE := by rw [hform]
    rw [pmOneMat_mulVec_jE] at h
    simp only [← Matrix.mulVec_mulVec] at h
    rw [hrow] at h
    simp only [Matrix.mulVec_smul, pmOneMat_mulVec_jE] at h
    exact h
  -- the diagonal entry is a unit with square one
  have hcc : c * c = 1 := by
    have h := congrFun hcol (Sum.inl 1)
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [mulVec_jE_apply] at h
    simpa [hc] using h
  -- hence the column is the diagonal one
  have hAe : M *ᵥ jE = c • jE := by
    have h : c • (c • (M *ᵥ jE)) = c • jE := by rw [hcol]
    rw [smul_smul, hcc, one_smul] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [← mulVec_jE_apply M (Sum.inl 0), hAe]; simp
  · rw [← mulVec_jE_apply M (Sum.inr 0), hAe]; simp
  · exact mul_self_eq_one_iff.mp hcc

end

end Work.Mostow

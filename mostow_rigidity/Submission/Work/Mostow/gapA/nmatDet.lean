import Mathlib
import Submission.Work.Mostow.gapA.nmatDefs
import Submission.Work.Mostow.gapA.axisPB

/-!
# The determinant of the normal action equals the determinant of the effective matrix

For a `g : PO 3 1` whose effective matrix `emat g` fixes the two boundary null vectors
`nvec a`, `nvec b`, the `2 × 2` matrix `nmat B g` of the action on the normal plane
`NormSub a b` has determinant equal to `(emat g).det`.  This is the general form of
`Work.Mostow.gapA.rotMat_det` (which assumes additionally that `(emat g).det = 1`).
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open _root_.Matrix

noncomputable section
variable {a b : E 3}

theorem nmatDet (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    (B : AxisBasis a b) (g : PO 3 1)
    (hfa : emat g *ᵥ nvec a = nvec a) (hfb : emat g *ᵥ nvec b = nvec b) :
    (nmat B g).det = (emat g).det := by
  have hgE1 : emat g *ᵥ B.E1 ∈ NormSub a b := emat_mulVec_mem_NormSub g hfa hfb B.mem1
  have hgE2 : emat g *ᵥ B.E2 ∈ NormSub a b := emat_mulVec_mem_NormSub g hfa hfb B.mem2
  obtain ⟨p, q, hpq⟩ := B.span (emat g *ᵥ B.E1) hgE1
  obtain ⟨r, s, hrs⟩ := B.span (emat g *ᵥ B.E2) hgE2
  have hp : nmat B g 0 0 = p := by rw [nmat_zero_zero, hpq, mink_smulE_E1]
  have hq : nmat B g 1 0 = q := by rw [nmat_one_zero, hpq, mink_smulE_E2]
  have hr : nmat B g 0 1 = r := by rw [nmat_zero_one, hrs, mink_smulE_E1]
  have hs : nmat B g 1 1 = s := by rw [nmat_one_one, hrs, mink_smulE_E2]
  have hdet : p * s - r * q = (emat g).det := by
    set bv : Fin 2 ⊕ Fin 2 → (Fin 3 ⊕ Fin 1 → ℝ) :=
      Sum.elim ![(nvec a), (nvec b)] ![(B.E1), (B.E2)] with hbv
    set D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
      Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
        (!![p, r; q, s] : Matrix (Fin 2) (Fin 2) ℝ) with hD
    set σ : Fin 3 ⊕ Fin 1 ≃ Fin 2 ⊕ Fin 2 :=
      (finSumFinEquiv (m := 3) (n := 1)).trans (finSumFinEquiv (m := 2) (n := 2)).symm with hσ
    set Aσ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
      fun i j => (emat g) (σ.symm i) (σ.symm j) with hAσ
    set C : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := fun i j => bv j (σ.symm i) with hC
    have hAσ_apply : ∀ a b : Fin 2 ⊕ Fin 2, Aσ a b = (emat g) (σ.symm a) (σ.symm b) :=
      fun a b => by rw [hAσ]
    have hC_apply : ∀ a b : Fin 2 ⊕ Fin 2, C a b = bv b (σ.symm a) := fun a b => by rw [hC]
    have hcol : ∀ j : Fin 2 ⊕ Fin 2, Matrix.mulVec (emat g) (bv j) = ∑ l, D l j • bv l := by
      rintro (i | i) <;> fin_cases i <;>
        simp only [hbv, hD, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
          cons_val_zero, cons_val_one, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
          Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply] <;>
        simp [hfa, hfb, hpq, hrs]
    have hCD : Aσ * C = C * D := by
      ext i j
      have h1 : (Aσ * C) i j = (Matrix.mulVec (emat g) (bv j)) (σ.symm i) := by
        rw [Matrix.mul_apply]
        simp only [hAσ_apply, hC_apply]
        rw [Equiv.sum_comp σ.symm (fun k => (emat g) (σ.symm i) k * (bv j) k)]
        rfl
      have h2 : (C * D) i j = (∑ l, D l j • bv l) (σ.symm i) := by
        rw [Matrix.mul_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [hC_apply]
        simp only [Pi.smul_apply]
        ring
      rw [h1, h2, hcol j]
    have hCdet : C.det ≠ 0 := by
      intro h0
      obtain ⟨v, hvne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      have hsum : (∑ j, v j • bv j) = 0 := by
        ext k
        obtain ⟨i, rfl⟩ := σ.symm.surjective k
        have h : (C *ᵥ v) i = 0 := by
          have := congrFun hv0 i
          simpa using this
        have h2 : (C *ᵥ v) i = (∑ j, v j • bv j) (σ.symm i) := by
          rw [show (C *ᵥ v) i = ∑ j, C i j * v j from rfl, Finset.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [hC_apply]
          simp only [Pi.smul_apply]
          ring
        rw [← h2]
        exact h
      have hind : v (Sum.inl 0) • nvec a + v (Sum.inl 1) • nvec b + v (Sum.inr 0) • B.E1
          + v (Sum.inr 1) • B.E2 = 0 := by
        rw [← hsum, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
        simp only [hbv, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one]
        abel
      obtain ⟨h1, h2, h3, h4⟩ := axisBasis_independentV (B := B) ha hb hab
        (v (Sum.inl 0)) (v (Sum.inl 1)) (v (Sum.inr 0)) (v (Sum.inr 1)) hind
      refine hvne (funext fun j => ?_)
      rcases j with j | j <;> fin_cases j
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have hAσdet : Aσ.det = (emat g).det := by
      have hsub : Aσ = (emat g).submatrix σ.symm σ.symm := by
        ext i j
        rw [hAσ_apply]
        rfl
      rw [hsub, Matrix.det_submatrix_equiv_self σ.symm (emat g)]
    have hDdet : D.det = (emat g).det := by
      have h := congrArg Matrix.det hCD
      simp only [Matrix.det_mul] at h
      rw [hAσdet] at h
      have h2 : C.det * D.det = C.det * (emat g).det := by
        rw [mul_comm (emat g).det C.det] at h
        exact h.symm
      exact mul_left_cancel₀ hCdet h2
    have hMD : (!![p, r; q, s] : Matrix (Fin 2) (Fin 2) ℝ).det = (emat g).det := by
      have hD' : D.det = (1 : Matrix (Fin 2) (Fin 2) ℝ).det
          * (!![p, r; q, s] : Matrix (Fin 2) (Fin 2) ℝ).det := by
        rw [hD]
        exact Matrix.det_fromBlocks_zero₁₂ _ _ _
      rw [hD', Matrix.det_one, one_mul] at hDdet
      exact hDdet
    simpa [Matrix.det_fin_two] using hMD
  have hrot : nmat B g = !![p, r; q, s] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, hs]
  rw [hrot, Matrix.det_fin_two]
  exact hdet

end

end Work.Mostow.gapA

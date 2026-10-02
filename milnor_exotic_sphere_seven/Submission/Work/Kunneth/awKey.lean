import Mathlib
import Submission.Work.Kunneth.AWAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pointwise Alexander--Whitney chain identity

For an `(n+1)`-simplex `(σ, τ)` of `X ⊗ Y` and an index `a : Fin (n+1)`, the `(a, n-a)`-component
of the Koszul differential of the Alexander--Whitney chain agrees with the `(a, n-a)`-component
of the Alexander--Whitney chain of the boundary of `(σ, τ)`.  This is the pointwise form of the
statement that `Work.Kunneth.awHom` is a chain map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth
noncomputable section
attribute [-instance] AddCommGroup.toIntModule

theorem awKey (X Y : SSet) (n : ℕ) (σ : X _⦋n+1⦌) (τ : Y _⦋n+1⦌) (a : Fin (n+1)) :
    awU X Y n a σ τ = awV X Y n a σ τ := by
  rw [awU, awV]
  set FP : X _⦋a.val+1⦌ := Work.Cohomology.frontFace X (a.val+1) (n+1) (by omega) σ with hFP
  set FP' : X _⦋a.val⦌ := Work.Cohomology.frontFace X a.val (n+1) (by omega) σ with hFP'
  set BF : Y _⦋n+1-(a.val+1)⦌ := backFaceLE Y (n+1-(a.val+1)) (n+1) (by omega) τ with hBF
  rw [d_genCh X a.val FP, d_genCh_pred_face Y (n+1-a.val) (by omega) (n+1) (by omega) τ]
  rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, ← Finset.sum_zsmul]
  simp only [smul_tmul_eq, tmul_smul_eq, ← mul_smul, ← pow_add]
  rw [Fin.sum_univ_castSucc (f := fun x : Fin (a.val+2) =>
        (-1 : ℤ)^x.val • (genCh X (X.δ x FP) ⊗ₜ[ℤ] genCh Y BF))]
  rw [Fin.sum_univ_succ (f := fun x : Fin ((n+1-a.val)+1) =>
        (-1 : ℤ)^(a.val + x.val) • (genCh X FP' ⊗ₜ[ℤ] genCh Y
          (Y.δ (⟨x.val, by omega⟩ : Fin (n+1-a.val-1+2))
            (backFaceLE Y (n+1-a.val-1+1) (n+1) (by omega) τ))))]
  -- the two leftover face terms
  have hlast : (ConcreteCategory.hom (SimplicialObject.δ X (Fin.last (a.val+1)))) FP = FP' := by
    have h1 : Fin.last (a.val+1) = (⟨a.val+1, by omega⟩ : Fin (a.val+2)) :=
      Fin.ext (by simp [Fin.val_last])
    rw [hFP, hFP', h1]
    exact delta_frontFace a.val (n - a.val) n (by omega) σ
  have hzero : (ConcreteCategory.hom (SimplicialObject.δ Y (⟨0, by omega⟩ : Fin (n+1-a.val-1+2))))
      (backFaceLE Y (n+1-a.val-1+1) (n+1) (by omega) τ) = BF := by
    rw [hBF]
    exact delta_zero_backFaceLE a.val (n+1-a.val-1) n (by omega) τ
  have hcancel : (-1 : ℤ)^(a.val+1) • (genCh X FP' ⊗ₜ[ℤ] genCh Y BF)
      + (-1 : ℤ)^(a.val+0) • (genCh X FP' ⊗ₜ[ℤ] genCh Y BF) = 0 := by
    rw [← add_zsmul]
    rw [show (-1 : ℤ)^(a.val+1) + (-1 : ℤ)^(a.val+0) = 0 from by
      rw [pow_succ]; ring]
    exact zero_zsmul _
  rw [hlast]
  simp only [Fin.val_zero]
  rw [hzero]
  rw [Fin.val_last]
  set T1 := ∑ i : Fin (a.val+1), (-1 : ℤ)^(i.castSucc.val) • (genCh X ((ConcreteCategory.hom (SimplicialObject.δ X i.castSucc)) FP) ⊗ₜ[ℤ] genCh Y BF) with hT1
  set A := (-1 : ℤ)^(a.val+1) • (genCh X FP' ⊗ₜ[ℤ] genCh Y BF) with hA
  set B := (-1 : ℤ)^(a.val+0) • (genCh X FP' ⊗ₜ[ℤ] genCh Y BF) with hB
  set T2 := ∑ i : Fin (n+1-a.val), (-1 : ℤ)^(a.val + i.succ.val) •
      (genCh X FP' ⊗ₜ[ℤ] genCh Y ((ConcreteCategory.hom (SimplicialObject.δ Y (⟨i.succ.val, by omega⟩ : Fin (n+1-a.val-1+2))))
        (backFaceLE Y (n+1-a.val-1+1) (n+1) (by omega) τ))) with hT2
  have hAB : A + B = 0 := by rw [hA, hB]; exact hcancel
  have hL : T1 + A + (B + T2) = T1 + T2 := by
    rw [show T1 + A + (B + T2) = T1 + (A + B) + T2 from by abel, hAB, add_zero]
  refine (show T1 + A + (B + T2) = T1 + T2 from hL).trans ?_
  -- define the target summand and split the other side
  let W : ℕ → tpSummand (sChain X) (sChain Y) a.val (n+1-a.val-1) := fun k =>
    if hk : k < n+2 then
      (-1 : ℤ)^k • (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ ⟨k,hk⟩ σ))
        ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n+1-a.val-1) n (by omega) (Y.δ ⟨k,hk⟩ τ)))
    else 0
  have h1 : (∑ i : Fin (a.val+1), (-1 : ℤ)^(i.castSucc.val) • (genCh X ((ConcreteCategory.hom (SimplicialObject.δ X i.castSucc)) FP) ⊗ₜ[ℤ] genCh Y BF))
      = ∑ i : Fin (a.val+1), W i.val := by
    apply Finset.sum_congr rfl
    intro i _
    have hc : i.castSucc = (⟨i.val, by omega⟩ : Fin (a.val+2)) := Fin.ext (by rw [Fin.val_castSucc])
    have hfpi : (ConcreteCategory.hom (SimplicialObject.δ X (⟨i.val, by omega⟩ : Fin (a.val+2)))) FP
        = Work.Cohomology.frontFace X a.val n (by omega)
            (X.δ (⟨i.val, by omega⟩ : Fin (n+2)) σ) := by
      rw [hFP]
      exact (frontFace_delta_le a.val (n - a.val) n (by omega) (⟨i.val, by omega⟩ : Fin (n+2))
        (by simp only [Fin.val_mk]; omega) σ).symm
    have hbfi : BF = backFaceLE Y (n+1-a.val-1) n (by omega)
        (Y.δ (⟨i.val, by omega⟩ : Fin (n+2)) τ) := by
      rw [hBF]
      exact (backFaceLE_delta_le a.val (n+1-a.val-1) n (by omega) (⟨i.val, by omega⟩ : Fin (n+2))
        (by simp only [Fin.val_mk]; omega) τ).symm
    simp only [W, dif_pos (show i.val < n+2 from by omega), Fin.val_castSucc]
    rw [hc, hfpi, hbfi]
    rfl
  have h2 : (∑ i : Fin (n+1-a.val), (-1 : ℤ)^(a.val + i.succ.val) •
        (genCh X FP' ⊗ₜ[ℤ] genCh Y ((ConcreteCategory.hom (SimplicialObject.δ Y (⟨i.succ.val, by omega⟩ : Fin (n+1-a.val-1+2))))
          (backFaceLE Y (n+1-a.val-1+1) (n+1) (by omega) τ))))
      = ∑ i : Fin (n+1-a.val), W (a.val+1+i.val) := by
    apply Finset.sum_congr rfl
    intro i _
    have hxi : FP' = Work.Cohomology.frontFace X a.val n (by omega)
        (X.δ (⟨a.val+1+i.val, by omega⟩ : Fin (n+2)) σ) := by
      rw [hFP']
      exact (frontFace_delta_ge a.val (n - a.val) n (by omega) (⟨a.val+1+i.val, by omega⟩ : Fin (n+2))
        (by simp only [Fin.val_mk]; omega) σ).symm
    have hfini : (⟨(⟨a.val+1+i.val, by omega⟩ : Fin (n+2)).val - a.val, by omega⟩ : Fin (n+1-a.val-1+2))
        = (⟨i.succ.val, by omega⟩ : Fin (n+1-a.val-1+2)) :=
      Fin.ext (by simp only [Fin.val_succ, Fin.val_mk]; omega)
    have hyi : (ConcreteCategory.hom (SimplicialObject.δ Y
          (⟨(⟨a.val+1+i.val, by omega⟩ : Fin (n+2)).val - a.val, by omega⟩ : Fin (n+1-a.val-1+2))))
        (backFaceLE Y (n+1-a.val-1+1) (n+1) (by omega) τ)
        = backFaceLE Y (n+1-a.val-1) n (by omega)
            (Y.δ (⟨a.val+1+i.val, by omega⟩ : Fin (n+2)) τ) := by
      exact (backFaceLE_delta_ge a.val (n+1-a.val-1) n (by omega) (⟨a.val+1+i.val, by omega⟩ : Fin (n+2))
        (by simp only [Fin.val_mk]; omega) τ).symm
    simp only [W, dif_pos (show a.val+1+i.val < n+2 from by omega)]
    rw [hxi, ← hfini, hyi]
    rw [show a.val + i.succ.val = a.val + 1 + i.val from by rw [Fin.val_succ]; omega]
  have hsplit : (∑ x : Fin (n+2), (-1 : ℤ)^x.val • (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ x σ)) ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n+1-a.val-1) n (by omega) (Y.δ x τ))))
      = (∑ i : Fin (a.val+1), W i.val) + (∑ i : Fin (n+1-a.val), W (a.val+1+i.val)) := by
    rw [show (∑ x : Fin (n+2), (-1 : ℤ)^x.val • (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ x σ)) ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n+1-a.val-1) n (by omega) (Y.δ x τ))))
        = ∑ x : Fin (n+2), W x.val from Finset.sum_congr rfl (fun x _ => by
          simp only [W, dif_pos (show x.val < n+2 from x.isLt)])]
    rw [Fin.sum_univ_eq_sum_range W (n+2)]
    rw [show (n+2) = (a.val+1) + (n+1-a.val) from by omega]
    rw [Finset.sum_range_add W (a.val+1) (n+1-a.val)]
    rw [← Fin.sum_univ_eq_sum_range W (a.val+1)]
    rw [← Fin.sum_univ_eq_sum_range (fun k => W (a.val+1+k)) (n+1-a.val)]
  rw [hsplit, hT1, hT2, h1, h2]

end
end Work.Kunneth

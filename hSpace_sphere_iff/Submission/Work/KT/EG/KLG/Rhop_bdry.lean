import Mathlib
import Submission.Work.KT.EG.KLG.kappa_bott_defs
import Submission.Work.KT.EG.KLG.Rhop_chart

namespace Work.KT.EG.KLG

open _root_.Matrix

set_option linter.unusedSimpArgs false

/-- The boundary restriction commutes with scalar multiplication of matrices, in the eta-expanded
form used by the statement of `Rhop_bdry`. -/
lemma bdry_smul_fun (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ}
    (c : C(X × Work.KT.Ball ℂ, ℂ))
    (B : Matrix (Fin n) (Fin n) C(X × Work.KT.Ball ℂ, ℂ)) :
    (c • B).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.bdryRestrict X c) • B.map (fun f => Work.KT.Fund.bdryRestrict X f) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, ContinuousMap.smul_apply, map_mul,
    ContinuousMap.mul_apply]
  rfl

/-- The two chart matrices of the Hopf projection have the same boundary restriction. -/
lemma chartMat_bdry (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    (!![1 + Work.KT.Fund.KL.zs X, Work.KT.Fund.KL.zcb X;
        Work.KT.Fund.KL.zc X, 1 - Work.KT.Fund.KL.zs X] :
        Matrix (Fin 2) (Fin 2) C(X × Work.KT.Ball ℂ, ℂ)).map
        (fun f => Work.KT.Fund.bdryRestrict X f)
      = (!![1 - Work.KT.Fund.KL.zs X, Work.KT.Fund.KL.zcb X;
          Work.KT.Fund.KL.zc X, 1 + Work.KT.Fund.KL.zs X] :
          Matrix (Fin 2) (Fin 2) C(X × Work.KT.Ball ℂ, ℂ)).map
        (fun f => Work.KT.Fund.bdryRestrict X f) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Work.KT.Fund.KL.bdryRestrict_zs]

theorem Rhop_bdry (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ((Work.KT.EG.KLG.R1 X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.EG.KLG.R2 X).map (fun f => Work.KT.Fund.bdryRestrict X f)) ∧
    ((Work.KT.Fund.KL.RhopUp X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.RhopDn X).map (fun f => Work.KT.Fund.bdryRestrict X f)) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
    · simp [Work.KT.EG.KLG.R1, Work.KT.EG.KLG.R2, Matrix.map_apply,
        Work.KT.Fund.KL.bdryRestrict_zs, Work.KT.Fund.KL.bdryRestrict_zc,
        Work.KT.Fund.KL.bdryRestrict_zcb, Work.KT.Fund.KL.bdryRestrict_zsinv]
  · rw [Work.KT.EG.KLG.RhopUp_chart X, Work.KT.EG.KLG.RhopDn_chart X]
    simp only [bdry_smul_fun X, chartMat_bdry X]

end Work.KT.EG.KLG

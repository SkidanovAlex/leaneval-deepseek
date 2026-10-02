import Mathlib
import Submission.Work.GenTwo.Bundles
import Submission.Work.Gen.gaugeBlock_inverse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# The block gauge of the Euler sequence of `ℂP²` and its inverse

The `n = 2` instance of `Submission/Work/Gen/EulerBlockInverse.lean`: `blockInv` is a two-sided
inverse of `blockFibre`, and consequently `MInvCLM` is a two-sided inverse of `MCLM`.
-/

namespace Work.Gen.E2

open Work.Projective

noncomputable section

theorem blockFibre_apply (p : Fin 3) (u : Fin 2 → ℂ)
    (ξ : EuclideanSpace ℂ (Fin (2 * 2))) (c : EuclideanSpace ℂ (Fin 2)) :
    blockFibre p u (ξ, c) =
      ((wlpC 3).symm (GblockCLM p u (holPart ξ, Work.Gen.c0CLM c)),
       (wlpC 3).symm (HblockCLM p u (antiPart ξ, Work.Gen.c1CLM c))) := rfl

theorem blkA_apply (p : Fin 3) (u : Fin 2 → ℂ)
    (w : EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :
    blkA p u w = (GblockInv p u (wlpC 3 w.1)).1 := rfl

theorem blkC_apply (p : Fin 3) (u : Fin 2 → ℂ)
    (w : EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :
    blkC p u w = (GblockInv p u (wlpC 3 w.1)).2 := rfl

theorem blkB_apply (p : Fin 3) (u : Fin 2 → ℂ)
    (w : EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :
    blkB p u w = (HblockInv p u (wlpC 3 w.2)).1 := rfl

theorem blkD_apply (p : Fin 3) (u : Fin 2 → ℂ)
    (w : EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :
    blkD p u w = (HblockInv p u (wlpC 3 w.2)).2 := rfl

theorem CbigInv_CbigCLM (y : EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :
    CbigInv (CbigCLM y) = y := by
  have h := congrArg (fun (f : (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ]
      (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3))) => f y) Cbig_inv.1
  simpa using h

theorem CbigCLM_CbigInv (y : EuclideanSpace ℂ (Fin (2 + (2 + 2)))) : CbigCLM (CbigInv y) = y := by
  have h := congrArg (fun (f : EuclideanSpace ℂ (Fin (2 + (2 + 2))) →L[ℂ]
      EuclideanSpace ℂ (Fin (2 + (2 + 2)))) => f y) Cbig_inv.2
  simpa using h

theorem holPart_XiEquivCLM (a b : Fin 2 → ℂ) :
    holPart (XiEquiv.toContinuousLinearMap (a, b)) = a := by
  rw [show XiEquiv.toContinuousLinearMap (a, b) = XiEquiv (a, b) from rfl, holPart_mk]

theorem antiPart_XiEquivCLM (a b : Fin 2 → ℂ) :
    antiPart (XiEquiv.toContinuousLinearMap (a, b)) = b := by
  rw [show XiEquiv.toContinuousLinearMap (a, b) = XiEquiv (a, b) from rfl, antiPart_mk]

theorem blockInv_blockFibre (p : Fin 3) (u : Fin 2 → ℂ)
    (ξ : EuclideanSpace ℂ (Fin (2 * 2))) (c : EuclideanSpace ℂ (Fin 2)) :
    blockInv p u (blockFibre p u (ξ, c)) = (ξ, c) := by
  have hA : blkA p u
      ((wlpC 3).symm (GblockCLM p u (holPart ξ, Work.Gen.c0CLM c)),
       (wlpC 3).symm (HblockCLM p u (antiPart ξ, Work.Gen.c1CLM c))) = holPart ξ := by
    rw [blkA_apply, ContinuousLinearEquiv.apply_symm_apply, GblockInv_GblockCLM]
  have hB : blkB p u
      ((wlpC 3).symm (GblockCLM p u (holPart ξ, Work.Gen.c0CLM c)),
       (wlpC 3).symm (HblockCLM p u (antiPart ξ, Work.Gen.c1CLM c))) = antiPart ξ := by
    rw [blkB_apply, ContinuousLinearEquiv.apply_symm_apply, HblockInv_HblockCLM]
  have hC : blkC p u
      ((wlpC 3).symm (GblockCLM p u (holPart ξ, Work.Gen.c0CLM c)),
       (wlpC 3).symm (HblockCLM p u (antiPart ξ, Work.Gen.c1CLM c))) = Work.Gen.c0CLM c := by
    rw [blkC_apply, ContinuousLinearEquiv.apply_symm_apply, GblockInv_GblockCLM]
  have hD : blkD p u
      ((wlpC 3).symm (GblockCLM p u (holPart ξ, Work.Gen.c0CLM c)),
       (wlpC 3).symm (HblockCLM p u (antiPart ξ, Work.Gen.c1CLM c))) = Work.Gen.c1CLM c := by
    rw [blkD_apply, ContinuousLinearEquiv.apply_symm_apply, HblockInv_HblockCLM]
  rw [blockInv, blockFibre_apply]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
  rw [hA, hB, hC, hD, Work.Gen.pair2CLM_c0_c1]
  exact Prod.ext (XiEquiv_holPart_antiPart ξ) rfl

theorem blockFibre_blockInv (p : Fin 3) (u : Fin 2 → ℂ)
    (w : EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :
    blockFibre p u (blockInv p u w) = w := by
  have hG : GblockInv p u (wlpC 3 w.1) = (blkA p u w, blkC p u w) := by
    rw [blkA_apply, blkC_apply]
  have hH : HblockInv p u (wlpC 3 w.2) = (blkB p u w, blkD p u w) := by
    rw [blkB_apply, blkD_apply]
  rw [blockInv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
  rw [blockFibre_apply]
  simp only [holPart_XiEquivCLM, Work.Gen.c0CLM_pair2, antiPart_XiEquivCLM,
    Work.Gen.c1CLM_pair2]
  rw [← hG, ← hH, GblockCLM_GblockInv, HblockCLM_HblockInv]
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply, Prod.mk.eta]

theorem blockInv_blockFibre' (p : Fin 3) (u : Fin 2 → ℂ)
    (y : EuclideanSpace ℂ (Fin (2 * 2)) × EuclideanSpace ℂ (Fin 2)) :
    blockInv p u (blockFibre p u y) = y := by
  obtain ⟨ξ, c⟩ := y
  exact blockInv_blockFibre p u ξ c

theorem blockFibre_blockInv' (p : Fin 3) (u : Fin 2 → ℂ)
    (y : EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :
    blockFibre p u (blockInv p u y) = y := blockFibre_blockInv p u y

theorem sumFibreC_symm_apply_apply
    (x : EuclideanSpace ℂ (Fin (2 * 2)) × EuclideanSpace ℂ (Fin 2)) :
    (Work.Whitney.sumFibreC (2 * 2) 2).symm.toContinuousLinearMap
      ((Work.Whitney.sumFibreC (2 * 2) 2).toContinuousLinearMap x) = x :=
  ContinuousLinearEquiv.symm_apply_apply _ x

theorem sumFibreC_apply_symm_apply (x : EuclideanSpace ℂ (Fin (2 * 2 + 2))) :
    (Work.Whitney.sumFibreC (2 * 2) 2).toContinuousLinearMap
      ((Work.Whitney.sumFibreC (2 * 2) 2).symm.toContinuousLinearMap x) = x :=
  ContinuousLinearEquiv.apply_symm_apply _ x

theorem MInvCLM_MCLM (p : Fin 3) (b : CP 2) :
    (MInvCLM p b).comp (MCLM p b) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
  rw [MInvCLM, MCLM]
  simp only [ContinuousLinearMap.comp_apply]
  rw [CbigInv_CbigCLM, blockInv_blockFibre', sumFibreC_apply_symm_apply]

theorem MCLM_MInvCLM (p : Fin 3) (b : CP 2) :
    (MCLM p b).comp (MInvCLM p b) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
  rw [MInvCLM, MCLM]
  simp only [ContinuousLinearMap.comp_apply]
  rw [sumFibreC_symm_apply_apply, blockFibre_blockInv', CbigCLM_CbigInv]

end

end Work.Gen.E2

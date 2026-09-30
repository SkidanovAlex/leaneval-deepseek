import Mathlib
import Submission.Work.FoldInst.FoldInvDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Matrix

namespace Work.FoldInst

/-- A Lorentz matrix has a genuine left inverse: `A⁻¹ * A = 1`.  The inverse is `J Aᵀ J`, whose
product with `A` is `J (Aᵀ J A) = J J = 1` by the defining relation `Aᵀ J A = J`. -/
private theorem foldInv_inv_mul {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : HypModel.IsLorentzMat A) :
    A⁻¹ * A = 1 := by
  have h : HypModel.J * Aᵀ * HypModel.J * A = 1 := by
    calc HypModel.J * Aᵀ * HypModel.J * A
        = HypModel.J * (Aᵀ * HypModel.J * A) := by noncomm_ring
      _ = HypModel.J * HypModel.J := by rw [hA.1]
      _ = 1 := foldInst_J_self_mul
  rw [Matrix.inv_eq_left_inv h]
  exact h

theorem foldInv_foldTheta (i : Fin 98) (r : Fin (foldCodim i) → Bool) {y : E4}
    (hy : y ∈ HypModel.ball) : foldInv i r (foldTheta i r y) = y := by
  have hM := foldInst_foldNr_mul_foldDrR_isLorentz i r
  have hinv := foldInv_inv_mul hM
  have h1 : HypModel.hypOfUHS (HypModel.mobiusKlein (foldNr i * foldDrR i r) y)
      = (foldNr i * foldDrR i r) *ᵥ HypModel.hypOfKlein y := by
    rw [HypModel.mobiusKlein]
    exact HypModel.hypOfUHS_uhsOfHyp
      (HypModel.isLorentzMat_mem_upperSheet hM (HypModel.hypOfKlein_mem_upperSheet hy))
  rw [foldInv, foldTheta, coordPermInv_comp_coordPerm, h1, Matrix.mulVec_mulVec, hinv,
    Matrix.one_mulVec, HypModel.kleinOfHyp_hypOfKlein hy]

end Work.FoldInst

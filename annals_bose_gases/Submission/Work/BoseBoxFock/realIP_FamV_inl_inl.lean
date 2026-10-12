import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.GramVDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.realIP_FamV_inl_inl` — the χ-row of the physical Gram

The `inl`-row of the physical Gram matrix of the honest mode family `FamV`: the
`realIP` pairing of the two χ-modes `Q(e^{ikx}χ_Λ)` is `ℓ³` times the coordinate
pairing `Work.BoseB4.gram (f k) (f k')` of the honest rows `f`.

This is *exactly* the χ-row of the defining property `HonestModes.hphys`
(`gram f k f k' = ℓ^{-3} · realIP (qVec k) (qVec k')`), transported across the
factor `ℓ³` (`ℓ = ellH v μ > 0`); the θ-rows (`Sum.inr`, where the condensate row
is the extra `δ_0`) are the content of the sibling statement `gramFamV`.
-/

noncomputable section

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- For `a ≠ 0`, the factor `a ^ 3` cancels the `ℤ`-power `a ^ (-(3 : ℤ))`. -/
private lemma pow_three_mul_neg_three (a b : ℝ) (ha : a ≠ 0) :
    a ^ 3 * (a ^ (-(3 : ℤ)) * b) = b := by
  have key : a ^ (-(3 : ℤ)) = (a ^ 3)⁻¹ := by
    rw [zpow_neg]
    exact congrArg Inv.inv (zpow_natCast a 3)
  rw [key, mul_inv_cancel_left₀ (pow_ne_zero 3 ha)]

theorem realIP_FamV_inl_inl (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (k k' : Lab HM.N) :
    Work.BoseK15.corpusBox.realIP (FamV v μ HM (Sum.inl k)) (FamV v μ HM (Sum.inl k'))
      = (ellH v μ) ^ 3 * Work.BoseB4.gram (HM.f k) (HM.f k') := by
  -- `FamV (inl k)` is `qVec` at the χ-momentum, so `hphys` is the statement with
  -- `realIP` and `gram` interchanged up to the factor `ℓ^{-3}`; cancel `ℓ³`.
  have h := HM.hphys k k'
  simp only [FamV] at h ⊢
  rw [h]
  exact (pow_three_mul_neg_three (ellH v μ) _ (ne_of_gt (ellH_pos v μ))).symm

end Work.BoseBoxFock

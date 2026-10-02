import Mathlib
import Submission.Work.Gen.EulerBlockInverse
import Submission.Work.Gen.gaugeBlock_inverse
import Submission.Work.Gen.tangentCoordChange_stdChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# The gauge identity of the block gauge

`Work.Gen.blockGauge`: on the overlap of the charts `p` and `q`, the block gauge
`blockFibre q (chartFun q b)` composed with the complexified tangent transition `cxTrans T_{p q}`
(the complexification of `E4 ∘ d(Phi p q) ∘ E4⁻¹`, where `T4` is the complexification of a
`ℂ`-linear map) equals the diagonal O(1)-scaling
`diag(homCoord 4 q p b, homCoord 4 p q b)` composed with `blockFibre p (chartFun p b)`.

This is the pointwise form of the Euler-sequence gauge, obtained from
`Work.Gen.holPart_cxTrans` / `Work.Gen.antiPart_cxTrans` and
`Work.Gen.Gblock_comp` / `Work.Gen.Hblock_comp`.
-/

namespace Work.Gen

open Work.Projective

noncomputable section

theorem Phi_chartFun (p q : Fin 5) {b : CP 4} (hb : b ∈ chartSet p) :
    Phi p q (chartFun p b) = chartFun q b := by
  rw [Phi, chartInv_chartFun p b hb]

theorem lam_chartFun (p q : Fin 5) {b : CP 4} (hb : b ∈ chartSet p) :
    lam p q (chartFun p b) = homCoord 4 p q b := by
  have h := homCoord_chartInv_eq (n := 4) p q (chartFun p b)
  rw [chartInv_chartFun p b hb] at h
  exact h.symm

theorem homCoord_inv_of_mem (p q : Fin 5) {b : CP 4} (hp : b ∈ chartSet p) (hq : b ∈ chartSet q) :
    homCoord 4 q p b = (homCoord 4 p q b)⁻¹ := by
  have h := homCoord_mul (n := 4) p q p hp hq hp
  rw [homCoord_self] at h
  have h1 : homCoord 4 q p b * homCoord 4 p q b = 1 := h.symm
  have hne : homCoord 4 p q b ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact one_ne_zero h1.symm
  calc homCoord 4 q p b = homCoord 4 q p b * 1 := (mul_one _).symm
    _ = homCoord 4 q p b * (homCoord 4 p q b * (homCoord 4 p q b)⁻¹) := by
          rw [mul_inv_cancel₀ hne]
    _ = (homCoord 4 q p b * homCoord 4 p q b) * (homCoord 4 p q b)⁻¹ := by rw [mul_assoc]
    _ = 1 * (homCoord 4 p q b)⁻¹ := by rw [h1]
    _ = (homCoord 4 p q b)⁻¹ := one_mul _

/-- **The gauge identity of the block gauge** (pointwise form). -/
theorem blockGauge (p q : Fin 5) {b : CP 4} (hb : b ∈ chartSet p ∩ chartSet q)
    (ξ : EuclideanSpace ℂ (Fin 8)) (c : EuclideanSpace ℂ (Fin 2)) :
    blockFibre q (chartFun q b) (Work.Thom.cxTrans (T4 (fderiv ℂ (Phi p q) (chartFun p b))) ξ, c)
      = ((homCoord 4 q p b) • (blockFibre p (chartFun p b) (ξ, c)).1,
         (homCoord 4 p q b) • (blockFibre p (chartFun p b) (ξ, c)).2) := by
  have hu : chartInv p (chartFun p b) ∈ chartSet q := by
    rw [chartInv_chartFun p b hb.1]; exact hb.2
  have hPh : Phi p q (chartFun p b) = chartFun q b := Phi_chartFun p q hb.1
  have hlam : lam p q (chartFun p b) = homCoord 4 p q b := lam_chartFun p q hb.1
  have hinv : homCoord 4 q p b = (lam p q (chartFun p b))⁻¹ := by
    rw [hlam, homCoord_inv_of_mem p q hb.1 hb.2]
  rw [blockFibre_apply, blockFibre_apply]
  refine Prod.ext ?_ ?_
  · refine ContinuousLinearEquiv.injective (wlpC 5) ?_
    simp only [ContinuousLinearEquiv.apply_symm_apply, map_smul]
    rw [holPart_cxTrans, GblockCLM_apply, ← hPh, Gblock_comp hu (holPart ξ) (c0CLM c), hinv,
      GblockCLM_apply]
  · refine ContinuousLinearEquiv.injective (wlpC 5) ?_
    simp only [ContinuousLinearEquiv.apply_symm_apply, map_smul]
    rw [antiPart_cxTrans, HblockCLM_eq, ← hPh, Hblock_comp hu (antiPart ξ) (c1CLM c), hlam,
      HblockCLM_eq]

end

end Work.Gen

import Mathlib
import Submission.Work.GenTwo.Bundles
import Submission.Work.GenTwo.BlockInverse

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
# The gauge identity of the block gauge at `n = 2`

The `n = 2` instance of `Submission/Work/Gen/EulerBlockGauge.lean`: on the overlap of the charts `p`
and `q`, the block gauge composed with the complexified tangent transition equals the block scaling
`diag(z_q/z_p, z_p/z_q)` composed with the block gauge.  This is read off from
`Work.Gen.holPart_cxTrans`/`antiPart_cxTrans` and `Work.Gen.Gblock_comp`/`Hblock_comp`.
-/

namespace Work.Gen.E2

open Work.Projective

noncomputable section

theorem Phi_chartFun (p q : Fin 3) {b : CP 2} (hb : b ∈ chartSet p) :
    Phi p q (chartFun p b) = chartFun q b := by
  rw [Phi, chartInv_chartFun p b hb]

theorem lam_chartFun (p q : Fin 3) {b : CP 2} (hb : b ∈ chartSet p) :
    lam p q (chartFun p b) = homCoord 2 p q b := by
  have h := homCoord_chartInv_eq (n := 2) p q (chartFun p b)
  rw [chartInv_chartFun p b hb] at h
  exact h.symm

theorem homCoord_inv_of_mem (p q : Fin 3) {b : CP 2} (hp : b ∈ chartSet p)
    (hq : b ∈ chartSet q) : homCoord 2 q p b = (homCoord 2 p q b)⁻¹ := by
  have h := homCoord_mul (n := 2) p q p hp hq hp
  rw [homCoord_self] at h
  have h1 : homCoord 2 q p b * homCoord 2 p q b = 1 := h.symm
  have hne : homCoord 2 p q b ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact one_ne_zero h1.symm
  calc homCoord 2 q p b = homCoord 2 q p b * 1 := (mul_one _).symm
    _ = homCoord 2 q p b * (homCoord 2 p q b * (homCoord 2 p q b)⁻¹) := by
          rw [mul_inv_cancel₀ hne]
    _ = (homCoord 2 q p b * homCoord 2 p q b) * (homCoord 2 p q b)⁻¹ := by rw [mul_assoc]
    _ = 1 * (homCoord 2 p q b)⁻¹ := by rw [h1]
    _ = (homCoord 2 p q b)⁻¹ := one_mul _

/-- **The gauge identity of the block gauge** (pointwise form). -/
theorem blockGauge (p q : Fin 3) {b : CP 2} (hb : b ∈ chartSet p ∩ chartSet q)
    (ξ : EuclideanSpace ℂ (Fin (2 * 2))) (c : EuclideanSpace ℂ (Fin 2)) :
    blockFibre q (chartFun q b) (Work.Thom.cxTrans (T (fderiv ℂ (Phi p q) (chartFun p b))) ξ, c)
      = ((homCoord 2 q p b) • (blockFibre p (chartFun p b) (ξ, c)).1,
         (homCoord 2 p q b) • (blockFibre p (chartFun p b) (ξ, c)).2) := by
  have hu : chartInv p (chartFun p b) ∈ chartSet q := by
    rw [chartInv_chartFun p b hb.1]; exact hb.2
  have hPh : Phi p q (chartFun p b) = chartFun q b := Phi_chartFun p q hb.1
  have hlam : lam p q (chartFun p b) = homCoord 2 p q b := lam_chartFun p q hb.1
  have hinv : homCoord 2 q p b = (lam p q (chartFun p b))⁻¹ := by
    rw [hlam, homCoord_inv_of_mem p q hb.1 hb.2]
  rw [blockFibre_apply, blockFibre_apply]
  refine Prod.ext ?_ ?_
  · refine ContinuousLinearEquiv.injective (wlpC 3) ?_
    simp only [ContinuousLinearEquiv.apply_symm_apply, map_smul]
    rw [holPart_cxTrans, GblockCLM_apply, ← hPh, Gblock_comp hu (holPart ξ) (Work.Gen.c0CLM c),
      hinv, GblockCLM_apply]
  · refine ContinuousLinearEquiv.injective (wlpC 3) ?_
    simp only [ContinuousLinearEquiv.apply_symm_apply, map_smul]
    rw [antiPart_cxTrans, HblockCLM_eq, ← hPh,
      Hblock_comp hu (antiPart ξ) (Work.Gen.c1CLM c), hlam, HblockCLM_eq]

end

end Work.Gen.E2

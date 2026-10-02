import Mathlib
import Submission.Work.ThomBordism.blockDetDefs
import Submission.Work.CofAtlas.phiDSplitBlocks

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.blockDet`

The block-determinant identity `Work.ThomBordism.CofAtlas.BlockDet` of the `(K1)` chapter, proved
from the block structure `Work.CofAtlas.phiDSplitBlocks`
(`phiD x p ∘ splitMap D x = prodMap id (Omega x p ∘ normFactor D x)`) by convolving the two
determinants (`LinearMap.det_comp`), removing the reference equivalence `rho` by conjugation
(`LinearMap.det_conj`) and splitting off the level block (`LinearMap.det_prodMap`,
`LinearMap.det_id`).
-/

set_option maxHeartbeats 800000

namespace Work.ThomBordism

open Work.ThomBordism.CofAtlas

theorem blockDet (k : ℕ) : Work.ThomBordism.CofAtlas.BlockDet k := by
  intro n M _ _ _ _ _ D x p hp hpint rho
  have hblocks := Work.CofAtlas.phiDSplitBlocks k n M D x p hp hpint
  -- The block structure as a single identity of linear maps.
  have hP : (D.phiD x (p : M)).toLinearMap ∘ₗ splitMap D x
      = LinearMap.prodMap (LinearMap.id : E9 →ₗ[ℝ] E9)
          ((D.Omega x (p : M)).toLinearMap ∘ₗ normFactor D x) := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨u, c⟩ := z
    rw [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.comp_apply,
      normFactor, LinearMap.comp_apply, LinearMap.inl_apply]
    exact Prod.ext (hblocks u c).1 (hblocks u c).2
  rw [← LinearMap.det_comp (rho.toLinearMap ∘ₗ (D.phiD x (p : M)).toLinearMap)
      ((splitMap D x) ∘ₗ rho.symm.toLinearMap)]
  have hconj : (rho.toLinearMap ∘ₗ (D.phiD x (p : M)).toLinearMap) ∘ₗ
        ((splitMap D x) ∘ₗ rho.symm.toLinearMap)
      = rho.toLinearMap ∘ₗ ((D.phiD x (p : M)).toLinearMap ∘ₗ splitMap D x) ∘ₗ
          rho.symm.toLinearMap := rfl
  rw [hconj, hP, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul]

end Work.ThomBordism

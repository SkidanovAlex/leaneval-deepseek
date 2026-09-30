import Mathlib
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.cuspTopUp_eq
import Submission.Work.Cusp.isOpenEmbedding_layerPtI
import Submission.Work.Cusp.isOpenEmbedding_cuspTopF
import Submission.Work.Cusp.isOpenMap_fillProj
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.isOpenEmbedding_layerPtSq
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.continuous_cuspCollarInv
import Submission.Work.Cusp.collarHeight_half
import Submission.Work.Space.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-- `cuspTopUp` unfolds to the composite `(layerPtI (cuspAnchor v c) × (tor ∘ mod)) ∘ cuspTopF`,
and each factor is an open map: `layerPtI` is an open embedding
(`isOpenEmbedding_layerPtI`), the `mod`-reduction to the torus factor is open
(`fillProj_torus_isOpenMap`), and `cuspTopF` is an open embedding
(`isOpenEmbedding_cuspTopF`).  Hence `cuspTopUp` is open. -/
theorem isOpenMap_cuspTopUp (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) : IsOpenMap (cuspTopUp a v D c δ hδ) := by
  rw [cuspTopUp_eq_comp]
  exact ((isOpenEmbedding_layerPtI (cuspAnchor v c)).isOpenMap.prodMap
    (fillProj_torus_isOpenMap a v D.tor)).comp
      (isOpenEmbedding_cuspTopF v c δ hδ).isOpenMap

end Work.Cusp

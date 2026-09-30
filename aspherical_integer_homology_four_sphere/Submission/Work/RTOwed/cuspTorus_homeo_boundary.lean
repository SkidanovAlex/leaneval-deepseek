import Mathlib
import Submission.Work.Cusp.slope_lattice
import Submission.Work.Cusp.cuspX_injOn
import Submission.Work.Cusp.isOpenEmbedding_layerPtI
import Submission.Work.Cusp.kv_ne_zero
import Submission.Work.Space.Assembly
import Submission.Work.Space.Split.retrAB_homotopyEquiv
import Submission.Work.RTOwed.cuspTorus_homeo_circle_torus
import Submission.Work.RTOwed.sqBoundary_homeo_circle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

theorem cuspTorus_homeo_boundary (v : Work.Space.Cusp) :
    Nonempty (Work.Cusp.CuspTorus v ≃ₜ
      {q : Work.Space.SquarePt × (Fin 2 → AddCircle (1 : ℝ)) // Work.Space.sqNorm q.1 = 1}) := by
  obtain ⟨h1⟩ := cuspTorus_homeo_circle_torus v
  obtain ⟨h2⟩ := sqBoundary_homeo_circle
  refine ⟨h1.trans ?_⟩
  refine (((Homeomorph.prodCongr h2 (Homeomorph.refl (Fin 2 → AddCircle (1 : ℝ)))).symm).trans ?_)
  exact (Work.Space.Split.subtypeProdHomeomorph
    (fun p : Work.Space.SquarePt => Work.Space.sqNorm p = 1)).symm

end Work.RTOwed

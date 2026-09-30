import Mathlib
import Submission.Work.RTOwed.FillCrossDef
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.atlas_junction_cover_polar
import Submission.Work.RTOwed.atlas_junction_cover_collar
import Submission.Work.RTOwed.atlas_collar_cover
import Submission.Work.RTOwed.core_cover_fin
import Submission.Work.RTOwed.fillCross_of_covers

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Work.RTInstance

theorem fillCross_of_rigid (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v)) :
    Nonempty (Work.RTOwed.FillCross g) := by
  obtain ⟨N₁, par₁, hpol⟩ := Work.RTOwed.atlas_junction_cover_polar (assemblyOf g) D
  obtain ⟨N₂, par₂, hcol⟩ := Work.RTOwed.atlas_junction_cover_collar (assemblyOf g) D
  obtain ⟨N₃, par₃, hδ, hne, hccol⟩ := Work.RTOwed.atlas_collar_cover (assemblyOf g) D
  obtain ⟨N₄, par₄, hkop, hksec, hcore⟩ :=
    Work.RTOwed.core_cover_fin (assemblyOf g) (fun w => (D w).tor)
  have hcore' : ∀ (v : Work.Space.Cusp)
      (q : Work.Space.SquarePt × (Work.RTInstance.assemblyOf g).Torus v),
      q ∈ Work.Cusp.coreLayer ((Work.RTInstance.assemblyOf g).Torus v) →
      ∃ i, (par₄ i).1 = v ∧ (Work.RTInstance.assemblyOf g).incW v q ∈
        (Work.RTOwed.kChartOf (Work.RTInstance.assemblyOf g) (fun w => (D w).tor)
          (par₄ i).1 (par₄ i).2 (hkop i) (hksec i)).source := by
    intro v q hq
    obtain ⟨i, hi, hmem⟩ := hcore v q hq
    refine ⟨i, hi, ?_⟩
    rw [← hi] at hmem
    rw [Work.RTOwed.kChartOf_source]
    rw [show v = (par₄ i).1 from hi.symm]
    simpa only [Set.image_univ] using hmem
  exact Work.RTOwed.fillCross_of_covers g D R N₁ par₁ hpol N₂ par₂ hcol N₃ par₃ hδ hne hccol
    N₄ par₄ hkop hksec hcore'

end Work.RTOwed

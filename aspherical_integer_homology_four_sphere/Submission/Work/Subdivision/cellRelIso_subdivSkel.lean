import Mathlib
import Submission.Work.Subdivision.SkelLevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Subdivision

theorem cellRelIso_subdivSkel (P : Work.Subdivision.PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (n : ℕ) (hf : ∀ k, (Work.Subdivision.PolyCW.cellRel P hdd n).sub k ≤
      ((Work.Subdivision.PolyCW.sdRel P n).sub k).comap
        ((Work.Subdivision.PolyCW.subdivSkel P hdd haug (n + 1)).f k).hom) :
    CategoryTheory.CategoryStruct.comp (Work.Subdivision.PolyCW.cellRelIso P hdd n).hom
        (Work.Subdivision.PolyCW.subdivSkel P hdd haug n) =
      CategoryTheory.CategoryStruct.comp
        ((Work.Subdivision.PolyCW.cellRel P hdd n).restrictMap
          (Work.Subdivision.PolyCW.sdRel P n)
          (Work.Subdivision.PolyCW.subdivSkel P hdd haug (n + 1)) hf)
        (Work.Subdivision.PolyCW.sdRelIso P n).hom := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

end Work.Subdivision

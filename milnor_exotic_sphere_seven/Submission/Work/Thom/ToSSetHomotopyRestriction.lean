import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Thom

open CategoryTheory MonoidalCategory Simplicial SimplicialObject Opposite in
theorem ToSSetHomotopyRestriction {X Y X' Y' : TopCat} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g') (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : H'.h ≫ v = (u ▷ TopCat.I) ≫ H.h) :
    H'.toSSet.h ≫ TopCat.toSSet.map v
      = (TopCat.toSSet.map u ▷ Δ[1]) ≫ H.toSSet.h := by
  simp only [TopCat.Homotopy.toSSet, Category.assoc]
  rw [← TopCat.toSSet.map_comp, h, TopCat.toSSet.map_comp,
      ← Functor.LaxMonoidal.μ_natural_left_assoc, MonoidalCategory.whisker_exchange_assoc]

end Work.Thom

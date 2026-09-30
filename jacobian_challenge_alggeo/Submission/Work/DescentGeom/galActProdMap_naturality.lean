/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Mathlib
import Submission.Work.DescentGeom.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Naturality of the diagonal Galois action on a product

The diagonal action `galActProdMap X Y gaX gaY hX hY σ` on a product `X ⊗ Y` of `k'`-schemes with
semilinear Galois actions (see `Work.DescentGeom.Basic`) is natural in the two factors: for
`σ`-equivariant morphisms `u : X ⟶ X'` and `v : Y ⟶ Y'` the square

```
X ⊗ Y --galActProdMap X Y --> X ⊗ Y
  |                                 |
 u⊗v                              u⊗v
  v                                 v
X'⊗ Y' -galActProdMap X' Y'-> X'⊗ Y'
```

commutes.  Both `galActProdMap` and `u ⊗ₘ v` are given by `pullback.map` (`galActProdMap` by
definition, `u ⊗ₘ v` through the monoidal structure on `Over (Spec k')`), so this is the
naturality of `pullback.map` in the two legs; it is proved by the universal property of the
pullback (`pullback.map_comp` composed with the two projections, where the equivariance `hu`, `hv`
of the legs enters).
-/

namespace Work.DescentGeom

open CategoryTheory Limits

open scoped CategoryTheory MonoidalCategory

set_option maxHeartbeats 800000

universe u

theorem galActProdMap_naturality {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X X' Y Y' : Work.DescentGeom.Sch k'} (u : X ⟶ X') (v : Y ⟶ Y')
    (gaX : Work.Descent.Gal k k' → (X.left ⟶ X.left))
    (gaX' : Work.Descent.Gal k k' → (X'.left ⟶ X'.left))
    (gaY : Work.Descent.Gal k k' → (Y.left ⟶ Y.left))
    (gaY' : Work.Descent.Gal k k' → (Y'.left ⟶ Y'.left))
    (hX : ∀ σ, gaX σ ≫ X.hom = X.hom ≫ Work.DescentGeom.specGal σ)
    (hX' : ∀ σ, gaX' σ ≫ X'.hom = X'.hom ≫ Work.DescentGeom.specGal σ)
    (hY : ∀ σ, gaY σ ≫ Y.hom = Y.hom ≫ Work.DescentGeom.specGal σ)
    (hY' : ∀ σ, gaY' σ ≫ Y'.hom = Y'.hom ≫ Work.DescentGeom.specGal σ)
    (hu : ∀ σ, gaX σ ≫ u.left = u.left ≫ gaX' σ)
    (hv : ∀ σ, gaY σ ≫ v.left = v.left ≫ gaY' σ) (σ : Work.Descent.Gal k k') :
    Work.DescentGeom.galActProdMap X Y gaX gaY hX hY σ ≫ (u ⊗ₘ v).left =
      (u ⊗ₘ v).left ≫ Work.DescentGeom.galActProdMap X' Y' gaX' gaY' hX' hY' σ := by
  simp only [galActProdMap, Over.tensorHom_left]
  rw [pullback.map_comp, pullback.map_comp]
  simp only [Category.comp_id, Category.id_comp, hu σ, hv σ]

end Work.DescentGeom

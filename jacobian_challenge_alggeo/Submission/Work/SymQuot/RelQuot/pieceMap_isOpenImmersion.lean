/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The "piece" inclusions `chartU U ⊗ ovV V ⟶ relQuotScheme X ⊗ Y` are open immersions

For the relative quotient property `Work.SymQuot.RelQuot.relQuot`, the source `X ⊗ Y` is covered
by the pieces `chartU U ⊗ ovV V` over the invariant affine charts `U` of `X` and the affine opens
`V ⊆ Y`.  This file records that each of the defining morphisms

`chartιOv D hbase U ⊗ₘ ovVι V : chartU D hbase U ⊗ ovV V ⟶ relQuotScheme X D hbase ⊗ Y`

is an open immersion of schemes, so that the pieces genuinely form an open cover of
`relQuotScheme X D hbase ⊗ Y` (compare `Work.SymQuot.RelQuot.pieceCover_mem`).

The point is that on underlying schemes the tensor product of morphisms in `Over (Spec K)` is the
`pullback.map` of the two components (`Over.tensorHom_left`), and a pullback of open immersions
along open immersions is an open immersion (`Scheme.pullback_map_isOpenImmersion`, the third
component being an identity, hence a monomorphism).  The two components here are
`chartιOv … .left = D.chartι U` (an open immersion, `QuotientData.chartι`) and
`ovVι V .left = V.1.ι` (an open immersion, `Scheme.Opens.ι`).
-/
import Mathlib
import Submission.Work.SymQuot.RelQuot.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1000000

namespace Work.SymQuot.RelQuot

universe u
open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem pieceMap_isOpenImmersion {K : Type u} [Field K] {X Y : Work.SpecLin.Sch K} {Γ : Type u}
    [Group Γ] [Fintype Γ] (D : Work.SymQuot.QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) (V : Y.left.affineOpens) :
    IsOpenImmersion (Work.SymQuot.RelQuot.chartιOv D hbase U ⊗ₘ
      Work.SymQuot.RelQuot.ovVι V).left := by
  -- On underlying schemes the tensor product of morphisms in `Over (Spec K)` is a `pullback.map`.
  rw [Over.tensorHom_left]
  simp only [chartιOv_left, ovVι_left]
  -- `D.chartι U` and `V.1.ι` are open immersions, and the identity is a monomorphism, so the
  -- pullback of the two open immersions is again an open immersion.
  exact Scheme.pullback_map_isOpenImmersion _ _ _ _ (D.chartι U) V.1.ι
    (𝟙 (Spec (CommRingCat.of K)))
    (by rw [Category.comp_id, chartU_hom])
    (by rw [Category.comp_id, ovV_hom])

end Work.SymQuot.RelQuot

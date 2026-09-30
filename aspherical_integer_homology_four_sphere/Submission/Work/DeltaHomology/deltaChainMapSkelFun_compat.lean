import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.SkeletonDefs
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.SkelChainDefs
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial

/-! ## Naturality of `TopCat.toSSetObjEquiv` and the corestriction of `χ`

The comparison map on the `k`-skeleton sends a simplex of `K.skel k` to the
singular simplex of the subspace `X^k ⊆ X` obtained by corestricting `χ`.  The
two auxiliary lemmas below relate this corestricted simplex to `χ` itself, which
is what makes the comparison map on the skeleton compatible with the comparison
map on `K`. -/

/-- Naturality of `TopCat.toSSetObjEquiv` with respect to a continuous map:
the singular simplex of `Y` obtained by pushing a singular simplex of `X`
forward along `g : X ⟶ Y` corresponds to the composite continuous map. -/
theorem singMap_comp_toSSetObjEquiv {X Y : TopCat} (g : X ⟶ Y) {n : ℕ}
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk n)) (singMap g x)
      = (ConcreteCategory.hom g).comp
          (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) x) := rfl

/-- The inclusion `X^k ⊆ X` composed with the corestricted characteristic map
of a simplex of dimension `≤ k` is the characteristic map itself. -/
theorem incl_comp_clsInSkelSet {K : DeltaCx} {X : TopCat} (χ : DeltaSimplexMap K X) (k : ℕ)
    {j : ℕ} (h : j ≤ k) (τ : Fin (K.card j)) :
    (ConcreteCategory.hom (incl (χ.skelSet k))).comp (χ.clsInSkelSet k h τ) = χ.cls j τ := by
  ext y
  exact χ.clsInSkelSet_coe k h τ y

/-- Pushing the corestricted singular simplex `χ.chiInSkelSet k h τ` (a simplex
of the subspace `X^k`) forward to `X` recovers the singular simplex `χ.χ j τ`. -/
theorem singMap_incl_chiInSkelSet {K : DeltaCx} {X : TopCat} (χ : DeltaSimplexMap K X) (k : ℕ)
    {j : ℕ} (h : j ≤ k) (τ : Fin (K.card j)) :
    singMap (incl (χ.skelSet k)) (χ.chiInSkelSet k h τ) = χ.χ j τ := by
  apply (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk j))).injective
  rw [show TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk j))
        (singMap (incl (χ.skelSet k)) (χ.chiInSkelSet k h τ))
      = (ConcreteCategory.hom (incl (χ.skelSet k))).comp
          (TopCat.toSSetObjEquiv (TopCat.of (χ.skelSet k)) (Opposite.op (SimplexCategory.mk j))
            (χ.chiInSkelSet k h τ)) from rfl]
  rw [show TopCat.toSSetObjEquiv (TopCat.of (χ.skelSet k)) (Opposite.op (SimplexCategory.mk j))
        (χ.chiInSkelSet k h τ) = χ.clsInSkelSet k h τ from rfl]
  rw [show TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk j)) (χ.χ j τ) = χ.cls j τ
        from rfl]
  exact incl_comp_clsInSkelSet χ k h τ

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise comparison map on the `k`-skeleton is compatible with the
comparison map on `K` and the inclusion of the skeleton `X^k ⊆ X`:

`χ.deltaChainMapSkelFun k j ≫ (inclChain ℤ X (χ.skelSet k)).f j
   = (K.skelHom k).chainMapFun j ≫ χ.deltaChainMapFun j`

(if `j ≤ k`, both sides send a basis simplex to the singular simplex `χ σ`, once on
the subspace `X^k` and once in `X`; if `j > k` the left-hand side is a map out of
the zero object, and the right-hand side is a `Sigma.desc` over the empty index
`Fin ((K.skel k).card j) = Fin 0`).

Route: check on `(K.skel k).chainι j σ` using
`DeltaSimplexMap.deltaChainMapSkelFun_chainι`, `DeltaCx.Hom.chainMapFun_chainι`,
`SSet.ι_chainComplexMap_f` (for the map induced by the inclusion of spaces,
`inclChain ℤ X (χ.skelSet k) = singChainMap ZMod (incl _)`) and the naturality of
`TopCat.toSSetObjEquiv` relating the singular simplex of a subspace to its image in
`X` (the corestriction `DeltaSimplexMap.clsInSkelSet_coe` on values). -/
theorem deltaChainMapSkelFun_compat {K : DeltaCx} {X : TopCat} (χ : DeltaSimplexMap K X)
    (k j : ℕ) :
    χ.deltaChainMapSkelFun k j ≫ (inclChain ZMod X (χ.skelSet k)).f j
      = (K.skelHom k).chainMapFun j ≫ χ.deltaChainMapFun j := by
  apply DeltaCx.chainX_hom_ext
  intro σ
  by_cases h : j ≤ k
  · -- Non-vacuous case `j ≤ k`: compute both sides on the basis simplex.
    rw [← Category.assoc, ← Category.assoc,
      DeltaSimplexMap.deltaChainMapSkelFun_chainι χ h σ,
      DeltaCx.Hom.chainMapFun_chainι (K.skelHom k) j σ,
      DeltaCx.skelHom_map]
    unfold inclChain
    rw [singChainMap_ι_apply]
    rw [singMap_incl_chiInSkelSet χ k h (skelMap K k σ),
        DeltaSimplexMap.deltaChainMapFun_chainι χ j (skelMap K k σ)]
  · -- Vacuous case `j > k`: `(K.skel k).card j = 0`, so there is no `σ`.
    exact Fin.elim0 (by rw [DeltaCx.skel_card_eq_zero K k (by omega)] at σ; exact σ)

end Work.DeltaHomology

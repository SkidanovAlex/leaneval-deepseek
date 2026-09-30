import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory

namespace Work.Domain.Engine

/-- The first comparison identity for the map `θ_γ` of `Work.Domain.PartialMap.theta`: the stalk map
of the first projection of the graph closure is a *section* of `θ_γ` over the canonical map
`O_{X,pr₁γ} ⟶ K(X)`.

Indeed `θ_γ` is "restrict a germ at `γ` to the generic point of the graph closure, then read it in
`K(X)`"; precomposing with `(pr₁).stalkMap γ` means restricting a germ at `pr₁ γ` first to `γ`,
and the composite with the identification `O_{Γ,toGraph η} ≅ O_{U,η} ≅ K(X)` is just the direct
restriction of a germ at `pr₁ γ` to the generic point of `X` — i.e. `algebraMap`.

The proof is a formal computation with the naturality lemmas for stalk maps:
`(pr₁).stalkMap γ ≫ Γ.stalkSpecializes h_γ = X.stalkSpecializes h₁ ≫ (pr₁).stalkMap (toGraph η)`
(`Scheme.Hom.stalkSpecializes_stalkMap`), the composition rule `Scheme.Hom.stalkMap_comp` for
`toGraph ≫ pr₁ = (g.domain).ι` (`Work.Domain.PartialMap.toGraph_pr₁`, transported along the
specialisation `Scheme.Hom.stalkMap_congr_hom`), and
`(g.domain).ι.stalkMap η ≫ (g.domain).stalkIso η = 𝟙` (`Scheme.Opens.stalkIso_inv`). -/
theorem comp_stalkMap {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g]
    (γ : Work.Domain.PartialMap.graph S g) :
    CategoryTheory.CategoryStruct.comp ((Work.Domain.PartialMap.pr₁ S g).stalkMap γ)
        (Work.Domain.PartialMap.theta g γ) =
      CommRingCat.ofHom (algebraMap
        (X.presheaf.stalk ((Work.Domain.PartialMap.pr₁ S g) γ)) X.functionField) := by
  -- Unfold `θ_γ`; from now on we compare with a stalk specialisation map.
  have key : (Work.Domain.PartialMap.pr₁ S g).stalkMap γ ≫ Work.Domain.PartialMap.theta g γ
      = X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
    -- The point of `Γ` above `η` is `toGraph η`; the point of `X` above it is the generic point.
    set_option backward.isDefEq.respectTransparency false in
    have key' : (Work.Domain.PartialMap.pr₁ S g).stalkMap γ ≫ Work.Domain.PartialMap.theta g γ
        = X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
      rw [Work.Domain.PartialMap.theta, Work.Domain.PartialMap.germMapToFunctionField]
      -- (1) move `(pr₁).stalkMap γ` past the specialisation to the generic point of `Γ`
      rw [← Category.assoc, ← AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap,
        Category.assoc]
      -- (2) reassociate so that `(pr₁).stalkMap (toGraph η) ≫ (toGraph).stalkMap η`
      nth_rewrite 2 [← Category.assoc]
      -- (3) combine the two stalk maps into `(toGraph ≫ pr₁).stalkMap η` and use
      --     `toGraph ≫ pr₁ = (g.domain).ι`, transporting along the specialisation;
      -- (4) `ι.stalkMap η` is the inverse of `g.domain.stalkIso η`
      rw [← AlgebraicGeometry.Scheme.Hom.stalkMap_comp,
        AlgebraicGeometry.Scheme.Hom.stalkMap_congr_hom
          (Work.Domain.PartialMap.toGraph S g ≫ Work.Domain.PartialMap.pr₁ S g)
          (g.domain.ι) (Work.Domain.PartialMap.toGraph_pr₁ S g),
        Category.assoc, ← AlgebraicGeometry.Scheme.Opens.stalkIso_inv, Iso.inv_hom_id,
        Category.comp_id, TopCat.Presheaf.stalkCongr_hom,
        TopCat.Presheaf.stalkSpecializes_comp]
    exact key'
  -- Compare with `algebraMap`, which *is* `X.presheaf.stalkSpecializes` to the generic point.
  rw [key]
  rfl

end Work.Domain.Engine

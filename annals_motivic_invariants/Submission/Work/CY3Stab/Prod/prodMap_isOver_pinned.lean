import Submission.Work.CY3Stab.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.prodMap_isOver_pinned` — `φ × id_{𝔸ᵏ}` is a map over `Spec 𝕜`

The product map `Work.CY3Stab.prodMap k φ` is the base change of `φ` along `𝔸ᵏ ⟶ Spec 𝕜`, hence a
map over `𝔸ᵏ` (`Work.CY3Stab.prodMap_spec`); composing with the structure morphism
`𝔸ᵏ ⟶ Spec 𝕜` shows that it is a map over `Spec 𝕜` — *provided* the `Over`-structure of the
cylinder is the canonical composite `𝔸ᵏ × X ⟶ 𝔸ᵏ ⟶ Spec 𝕜` (`Work.CY3Stab.wProdOver`).  That
pinning is exactly what the two hypotheses `hX`, `hY` record; at the call sites of this directory
they are discharged by `pullback.condition` (or by `rfl`, when the cylinder `Variety`-structure is
`Work.CY3Stab.varietyWProd`, whose `over` field *is* `wProdOver`).  Without the pinning the
statement is false: an arbitrary `Variety`-structure on the cylinder may have a different structure
morphism (see `Submission/Work/CY3Stab/Prod/cInv_prodMap_eq_zero_of_strong.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The product map is over the base field**, for cylinder `Over`-structures pinned to the
canonical composite `Work.CY3Stab.wProdOver`.

`prodMap k φ` is the base change of `φ` along `𝔸ᵏ ⟶ Spec 𝕜`, hence over `𝔸ᵏ`
(`Work.CY3Stab.prodMap_spec`); composing with the structure morphism `𝔸ᵏ ⟶ Spec 𝕜` gives that it
is over `Spec 𝕜`.  The pinning hypotheses `hX`, `hY` are what make the statement correct: the
common structure morphism of the cylinder is the composite, and without pinning an *arbitrary*
`Variety`-structure on the cylinder (whose `over` field is not the composite) makes the claim
false.  They are discharged at the call sites by `pullback.condition`, see below. -/
theorem prodMap_isOver_pinned {𝕜 : Type} [Field 𝕜] (k : ℕ) {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y]
    (φ : X.BirationalMap Y) [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    (hX : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      = (Work.CY3Stab.wProdOver (𝕜 := 𝕜) X k).1)
    (hY : (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      = (Work.CY3Stab.wProdOver (𝕜 := 𝕜) Y k).1) :
    (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := by
  obtain ⟨g, hgover, hgtr⟩ :=
    (Work.CY3Stab.prodMap_spec (𝕜 := 𝕜) k φ).1.exists_partialMap_over
  refine ⟨g, ?_, hgtr⟩
  have hgA : (g.compHom (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k ↘ Work.CY3Stab.AffineK (𝕜 := 𝕜) k)).hom
      = g.domain.ι ≫ (Work.CY3Stab.WProd (𝕜 := 𝕜) X k ↘ Work.CY3Stab.AffineK (𝕜 := 𝕜) k) :=
    AlgebraicGeometry.Scheme.PartialMap.isOver_iff.mp hgover
  rw [AlgebraicGeometry.Scheme.PartialMap.compHom_hom] at hgA
  rw [AlgebraicGeometry.Scheme.PartialMap.isOver_iff,
    AlgebraicGeometry.Scheme.PartialMap.compHom_hom]
  rw [show (Work.CY3Stab.WProd (𝕜 := 𝕜) X k ↘ Work.CY3Stab.AffineK (𝕜 := 𝕜) k)
      = pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (X ↘ Spec (CommRingCat.of 𝕜)) from rfl,
    show (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k ↘ Work.CY3Stab.AffineK (𝕜 := 𝕜) k)
      = pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (Y ↘ Spec (CommRingCat.of 𝕜)) from rfl] at hgA
  rw [hX, hY,
    show (Work.CY3Stab.wProdOver (𝕜 := 𝕜) X k).1
      = pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (X ↘ Spec (CommRingCat.of 𝕜)) ≫
          (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) from rfl,
    show (Work.CY3Stab.wProdOver (𝕜 := 𝕜) Y k).1
      = pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (Y ↘ Spec (CommRingCat.of 𝕜)) ≫
          (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) from rfl]
  rw [← Category.assoc, ← Category.assoc, hgA, Category.assoc]


end

end Work.CY3Stab.Prod

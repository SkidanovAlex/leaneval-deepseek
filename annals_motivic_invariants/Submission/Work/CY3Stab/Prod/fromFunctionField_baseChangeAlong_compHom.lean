import Mathlib
import Submission.Work.CY3Stab.Prod.CylFF
import Submission.Work.K3.BaseChangeBirational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.fromFunctionField_baseChangeAlong_compHom`

The compatibility of the germ at the generic point (`Scheme.PartialMap.fromFunctionField`) with the
base change of a partial map along the projection `𝔸ᵏ ⟶ Spec 𝕜`:

> `fromFunctionField (baseChangeAlong (𝔸ᵏ ⟶ Spec 𝕜) g ∘_{pullback.snd} π_𝔸ᵏ×Y)`
> `= Spec.map (cylFFMap X k) ≫ fromFunctionField g`

i.e. the germ at the generic point of `𝔸ᵏ ×_𝕜 X` of the base-changed partial map, followed by the
projection `𝔸ᵏ ×_𝕜 Y ⟶ Y`, is the pullback — along the function field extension
`K(X) ⟶ K(𝔸ᵏ ×_𝕜 X)` of the cylinder projection (`Work.CY3Stab.Prod.cylFFMap`) — of the germ of
`g`.

Mathematically this is the naturality of `Spec` on stalks:
`W.fromSpecStalk η ≫ p = Spec.map (p.stalkMap η) ≫ X.fromSpecStalk (p η)` for `η` the generic point
of `W = 𝔸ᵏ ×_𝕜 X`, combined with the fact that `cylFFMap X k` is the fraction field lift of
`p.stalkMap η` (`Work.CY3Stab.Prod.ffAlgMap_cylFFMap`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **`fromFunctionField` of a right-composition with a morphism.**  The germ of `f.compHom g` at
the generic point is the germ of `f` followed by `g`. -/
theorem fromFunctionField_compHom {X Y Z : Scheme.{0}} [IrreducibleSpace X]
    (f : X.PartialMap Y) (g : Y ⟶ Z) :
    (f.compHom g).fromFunctionField = f.fromFunctionField ≫ g := by
  have hmem : genericPoint X ∈ (f.compHom g).domain :=
    (genericPoint_specializes _).mem_open (f.compHom g).domain.2
      (f.compHom g).dense_domain.nonempty.choose_spec
  rw [← PartialMap.fromFunctionField_eq_fromSpecStalkOfMem (f := f.compHom g) hmem,
    ← PartialMap.fromFunctionField_eq_fromSpecStalkOfMem (f := f) hmem,
    Scheme.PartialMap.fromSpecStalkOfMem_compHom]

/-- **The germ at the generic point of the cylinder projection is `Spec.map` of `cylFFMap`.**

Writing `W = 𝔸ᵏ ×_𝕜 X` and `p : W ⟶ X` for the projection, the naturality of `Spec` on stalks at
the generic point `η` of `W` gives
`W.fromSpecStalk η ≫ p = Spec.map (p.stalkMap η) ≫ X.fromSpecStalk (p η)`; and `p.stalkMap η` is
`ffAlgMap X (p η) ≫ cylFFMap X k` by the defining property of `cylFFMap`
(`Work.CY3Stab.Prod.ffAlgMap_cylFFMap`).  Since `p η` is specialised by the generic point of `X`,
`Spec.map (ffAlgMap X (p η)) ≫ X.fromSpecStalk (p η) = X.fromSpecStalk (genericPoint X)`. -/
theorem fromSpecStalk_cylProj_genericPoint (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))]
    (k : ℕ) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral (WProd (𝕜 := 𝕜) X k)]
    [IrreducibleSpace (WProd (𝕜 := 𝕜) X k)] :
    (WProd (𝕜 := 𝕜) X k).fromSpecStalk (genericPoint (WProd (𝕜 := 𝕜) X k)) ≫ cylProj (𝕜 := 𝕜) X k
      = Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ X.fromSpecStalk (genericPoint X) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk (f := cylProj (𝕜 := 𝕜) X k)
    (x := genericPoint (WProd (𝕜 := 𝕜) X k))]
  rw [← ffAlgMap_cylFFMap (𝕜 := 𝕜) X k]
  rw [Spec.map_comp, Category.assoc, ffAlgMap_eq_stalkSpecializes,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- **The requested lemma.**  The germ at the generic point of the base change of `g` along the
projection `𝔸ᵏ ⟶ Spec 𝕜`, followed by the projection `𝔸ᵏ ×_𝕜 Y ⟶ Y`, is the pullback along
`cylFFMap X k` of the germ of `g`. -/
theorem fromFunctionField_baseChangeAlong_compHom
    {𝕜 : Type} [Field 𝕜] {X Y : AlgebraicGeometry.Scheme.{0}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (k : ℕ) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [IrreducibleSpace (Work.K3.baseChangeAlong
        (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k)) X)]
    (g : X.PartialMap Y) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] :
    ((Work.K3.PartialMap.baseChangeAlong
        (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k)) g).compHom
        (CategoryTheory.Limits.pullback.snd
          (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k))
          (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) Y))).fromFunctionField
      = CategoryTheory.CategoryStruct.comp
          (AlgebraicGeometry.Spec.map (Work.CY3Stab.Prod.cylFFMap (𝕜 := 𝕜) X k))
          (AlgebraicGeometry.Scheme.PartialMap.fromFunctionField g) := by
  -- Rewrite the goal in the (definitionally equal) spelling matching `Work.K3.baseChangeAlong`,
  -- whose internals use `↘` (`CategoryTheory.over`).
  show ((Work.K3.PartialMap.baseChangeAlong
        (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).compHom
        (pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
          (Y ↘ Spec (CommRingCat.of 𝕜)))).fromFunctionField
      = CategoryTheory.CategoryStruct.comp
          (Spec.map (cylFFMap (𝕜 := 𝕜) X k)) (g.fromFunctionField)
  rw [fromFunctionField_compHom]
  -- The germ comparison, stated both with the explicit preimage (for the internal rewriting)
  -- and with the domain of the base-changed partial map (for the outer composition).
  have hMp : ∀ (hη : genericPoint (Work.K3.baseChangeAlong
          (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) X) ∈
        (pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (X ↘ Spec (CommRingCat.of 𝕜)) ⁻¹ᵁ g.domain))
      (hξ : genericPoint X ∈ g.domain),
      (pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (X ↘ Spec (CommRingCat.of 𝕜)) ⁻¹ᵁ g.domain).fromSpecStalkOfMem
          (genericPoint (Work.K3.baseChangeAlong
            (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) X)) hη
        ≫ (pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (X ↘ Spec (CommRingCat.of 𝕜)) ∣_ g.domain)
      = Spec.map (cylFFMap (𝕜 := 𝕜) X k)
        ≫ g.domain.fromSpecStalkOfMem (genericPoint X) hξ := by
    intro hη hξ
    rw [← cancel_mono g.domain.ι]
    rw [Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact fromSpecStalk_cylProj_genericPoint X k
  have hM : ∀ (hη : genericPoint (Work.K3.baseChangeAlong
          (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) X) ∈
        (Work.K3.PartialMap.baseChangeAlong
          (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).domain)
      (hξ : genericPoint X ∈ g.domain),
      (Work.K3.PartialMap.baseChangeAlong
            (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).domain.fromSpecStalkOfMem
          (genericPoint (Work.K3.baseChangeAlong
            (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) X)) hη
        ≫ (pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (X ↘ Spec (CommRingCat.of 𝕜)) ∣_ g.domain)
      = Spec.map (cylFFMap (𝕜 := 𝕜) X k)
        ≫ g.domain.fromSpecStalkOfMem (genericPoint X) hξ := fun hη hξ => hMp hη hξ
  have hhom : (Work.K3.PartialMap.baseChangeAlong
          (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).hom
        ≫ pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (Y ↘ Spec (CommRingCat.of 𝕜))
      = (pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
            (X ↘ Spec (CommRingCat.of 𝕜)) ∣_ g.domain)
        ≫ g.hom :=
    Work.K3.PartialMap.baseChangeAlong_hom_snd _ _
  have hspecη : genericPoint (Work.K3.baseChangeAlong
        (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) X) ∈
      (Work.K3.PartialMap.baseChangeAlong
        (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).domain :=
    (genericPoint_specializes _).mem_open
      (Work.K3.PartialMap.baseChangeAlong
        (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).domain.2
      (Work.K3.PartialMap.baseChangeAlong
        (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).dense_domain.nonempty.choose_spec
  have hspecξ : genericPoint X ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  rw [← PartialMap.fromFunctionField_eq_fromSpecStalkOfMem
        (f := Work.K3.PartialMap.baseChangeAlong
          (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g) hspecη]
  rw [show (Work.K3.PartialMap.baseChangeAlong
          (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).fromSpecStalkOfMem hspecη
      = (Work.K3.PartialMap.baseChangeAlong
            (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).domain.fromSpecStalkOfMem
          (genericPoint (Work.K3.baseChangeAlong
            (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) X)) hspecη
        ≫ (Work.K3.PartialMap.baseChangeAlong
            (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) g).hom from rfl]
  rw [← PartialMap.fromFunctionField_eq_fromSpecStalkOfMem (f := g) hspecξ]
  rw [show g.fromSpecStalkOfMem hspecξ
      = g.domain.fromSpecStalkOfMem (genericPoint X) hspecξ ≫ g.hom from rfl]
  rw [Category.assoc]
  rw [hhom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ g.hom) (hM hspecη hspecξ)).trans (Category.assoc _ _ _))

end

end Work.CY3Stab.Prod

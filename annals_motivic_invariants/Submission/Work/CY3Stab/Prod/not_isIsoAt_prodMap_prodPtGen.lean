import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.CY3Stab.Prod.ProdFibDefs
import Submission.Work.CY3Stab.Prod.SecAt
import Submission.Work.Motivic.isIsoAt_of_mutual_inverse
import Submission.Work.CY3Stab.Prod.exists_partialMap_mem_domain_of_prodPt_mem_domain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- The germ of a partial map at a point of its domain, evaluated at the closed point of
`Spec 𝒪_x`, is the value of the map at `x`. -/
theorem PartialMap.fromSpecStalkOfMem_closedPoint {X Y : AlgebraicGeometry.Scheme.{0}}
    (f : X.PartialMap Y) {x : X} (hx : x ∈ f.domain) :
    f.fromSpecStalkOfMem hx (IsLocalRing.closedPoint (X.presheaf.stalk x)) =
      f.hom ⟨x, hx⟩ := by
  have h2 : f.domain.fromSpecStalkOfMem x hx (IsLocalRing.closedPoint (X.presheaf.stalk x))
      = ⟨x, hx⟩ := by
    apply Subtype.ext
    show f.domain.ι ((f.domain.fromSpecStalkOfMem x hx)
      (IsLocalRing.closedPoint (X.presheaf.stalk x))) = x
    rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.fromSpecStalk_closedPoint]
  change f.hom (f.domain.fromSpecStalkOfMem x hx (IsLocalRing.closedPoint (X.presheaf.stalk x)))
    = f.hom ⟨x, hx⟩
  rw [h2]

/-- The canonical map `Spec 𝒪_{WX,y} ⟶ Spec 𝒪_{X,x}` (`p y = x`) sends the closed point to the
closed point. -/
theorem closedPoint_stalkMap {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) (y : X) :
    AlgebraicGeometry.Spec.map (f.stalkMap y)
      (IsLocalRing.closedPoint (X.presheaf.stalk y)) =
      (IsLocalRing.closedPoint (Y.presheaf.stalk (f y))) :=
  IsLocalRing.comap_closedPoint (f.stalkMap y).hom

/-- **The requested lemma.**  If `φ : X ⤏ Y` is a birational map over `𝕜` which is *not* an
isomorphism at the point `x`, then the product map `φ × id_{𝔸ᵏ}` is not an isomorphism at the
cylinder point `prodPt X x k` (the generic point of the fibre of `p : 𝔸ᵏ × X ⟶ X` over `x`). -/
theorem not_isIsoAt_prodMap_prodPtGen (𝕜 : Type) [Field 𝕜] (k : ℕ) {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y] (φ : X.BirationalMap Y)
    [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    (x : X) [IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor]
    (hx : ¬ IsIsoAt φ x) :
    ¬ IsIsoAt (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ)
      ((Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo
        (⊥ : PrimeSpectrum (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor)) := by
  haveI hLOFX : AlgebraicGeometry.LocallyOfFiniteType (overHom (𝕜 := 𝕜) X) :=
    show AlgebraicGeometry.LocallyOfFiniteType (X ↘ Spec (CommRingCat.of 𝕜)) from
      ‹MotivicInvariants.Variety 𝕜 X›.locallyOfFiniteType
  haveI hLOFY : AlgebraicGeometry.LocallyOfFiniteType (overHom (𝕜 := 𝕜) Y) :=
    show AlgebraicGeometry.LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of 𝕜)) from
      ‹MotivicInvariants.Variety 𝕜 Y›.locallyOfFiniteType
  haveI hSepX : AlgebraicGeometry.IsSeparated (overHom (𝕜 := 𝕜) X) :=
    show AlgebraicGeometry.IsSeparated (X ↘ Spec (CommRingCat.of 𝕜)) from
      ‹MotivicInvariants.Variety 𝕜 X›.isSeparated
  haveI hSepY : AlgebraicGeometry.IsSeparated (overHom (𝕜 := 𝕜) Y) :=
    show AlgebraicGeometry.IsSeparated (Y ↘ Spec (CommRingCat.of 𝕜)) from
      ‹MotivicInvariants.Variety 𝕜 Y›.isSeparated
  intro h
  set ξ : Work.CY3Stab.WProd (𝕜 := 𝕜) X k :=
    (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo
      (⊥ : PrimeSpectrum (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor) with hξdef
  obtain ⟨i, hξmem, hi⟩ := h
  -- partial map representatives over 𝕜
  obtain ⟨g₀, hg₀over, hg₀eq⟩ :=
    RationalMap.exists_partialMap_over (S := AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      (f := φ.hom)
  obtain ⟨k₀, hk₀over, hk₀eq⟩ :=
    RationalMap.exists_partialMap_over (S := AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      (f := φ.inv)
  haveI : g₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := hg₀over
  haveI : k₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := hk₀over
  -- projections
  have hsndX : pullback.snd (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k)) (overHom (𝕜 := 𝕜) X)
      = pullback.snd (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k)) (overHom (𝕜 := 𝕜) X) := rfl
  set sndX : Work.CY3Stab.WProd (𝕜 := 𝕜) X k ⟶ X :=
    pullback.snd (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k)) (overHom (𝕜 := 𝕜) X) with hsndX'
  set sndY : Work.CY3Stab.WProd (𝕜 := 𝕜) Y k ⟶ Y :=
    pullback.snd (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k)) (overHom (𝕜 := 𝕜) Y) with hsndY'
  let Gf : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).PartialMap Y := i.toPartialMap.compHom sndY
  let Gb : (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k).PartialMap X := i.symm.toPartialMap.compHom sndX
  let ξ' : Work.CY3Stab.WProd (𝕜 := 𝕜) Y k := (i.iso.hom ⟨ξ, hξmem⟩).1
  have hξ'mem : ξ' ∈ i.target := (i.iso.hom ⟨ξ, hξmem⟩).2
  have hξmemGf : ξ ∈ Gf.domain := hξmem
  have hξ'memGb : ξ' ∈ Gb.domain := hξ'mem
  -- the two rational maps of the involved partial maps
  have hsymm : i.symm.toRationalMap = (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).inv := by
    have h1 : PartialIso.toBirationalMap i = Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ :=
      BirationalMap.ext _ _ (by rw [PartialIso.toBirationalMap_hom, hi])
    have h2 := congrArg (fun (f : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).BirationalMap
        (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)) => f.inv) h1
    simpa using h2
  have heq_f : Gf.toRationalMap =
      ((Work.K3.PartialMap.baseChangeAlong (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k)) g₀).compHom
        sndY).toRationalMap := by
    have h1 : (Work.K3.PartialMap.baseChangeAlong (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k))
        g₀).toRationalMap = (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).hom :=
      (prodMap_spec (𝕜 := 𝕜) k φ).2.1 g₀ hg₀eq
    have hi' : i.toPartialMap.toRationalMap = (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).hom := hi
    show (i.toPartialMap.compHom sndY).toRationalMap
      = ((Work.K3.PartialMap.baseChangeAlong (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k)) g₀).compHom
        sndY).toRationalMap
    rw [RationalMap.compHom_toRationalMap, hi', RationalMap.compHom_toRationalMap, h1]
  have heq_b : Gb.toRationalMap =
      ((Work.K3.PartialMap.baseChangeAlong (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k)) k₀).compHom
        sndX).toRationalMap := by
    have h1 : (Work.K3.PartialMap.baseChangeAlong (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k))
        k₀).toRationalMap = (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).inv :=
      (prodMap_spec (𝕜 := 𝕜) k φ).2.2 k₀ hk₀eq
    have hi' : i.symm.toPartialMap.toRationalMap = (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).inv :=
      hsymm
    show (i.symm.toPartialMap.compHom sndX).toRationalMap
      = ((Work.K3.PartialMap.baseChangeAlong (overHom (𝕜 := 𝕜) (AffineK (𝕜 := 𝕜) k)) k₀).compHom
        sndX).toRationalMap
    rw [RationalMap.compHom_toRationalMap, hi', RationalMap.compHom_toRationalMap, h1]
  -- the two crux applications
  have key_f : ∃ (g : X.PartialMap Y) (hxg : sndX ξ ∈ g.domain),
      g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) ∧
        g.toRationalMap = g₀.toRationalMap ∧
        Gf.fromSpecStalkOfMem hξmemGf =
          CategoryStruct.comp (AlgebraicGeometry.Spec.map (sndX.stalkMap ξ))
            (g.fromSpecStalkOfMem hxg) :=
    exists_partialMap_mem_domain_of_prodPt_mem_domain k ξ g₀ Gf heq_f hξmemGf
  obtain ⟨g, hxg, hgover, hgrat, hgerm⟩ := key_f
  have key_b : ∃ (k' : Y.PartialMap X) (hyk : sndY ξ' ∈ k'.domain),
      k'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) ∧
        k'.toRationalMap = k₀.toRationalMap ∧
        Gb.fromSpecStalkOfMem hξ'memGb =
          CategoryStruct.comp (AlgebraicGeometry.Spec.map (sndY.stalkMap ξ'))
            (k'.fromSpecStalkOfMem hyk) :=
    exists_partialMap_mem_domain_of_prodPt_mem_domain k ξ' k₀ Gb heq_b hξ'memGb
  obtain ⟨k', hyk, hkover, hkrat, hkgerm⟩ := key_b
  -- the point x in the domain of g
  have hxs : sndX ξ = x := by
    simp only [hsndX', hξdef]
    exact prodPt_snd X x k
  have hxg' : x ∈ g.domain := hxs ▸ hxg
  -- values
  have hptf : i.toPartialMap.hom ⟨ξ, hξmemGf⟩ = ξ' := by
    show i.target.ι (i.iso.hom ⟨ξ, hξmemGf⟩) = (i.iso.hom ⟨ξ, hξmem⟩).1
    have he : (⟨ξ, hξmemGf⟩ : i.source.toScheme) = ⟨ξ, hξmem⟩ := Subtype.ext rfl
    rw [he]
    rfl
  have hvalGf : Gf.hom ⟨ξ, hξmemGf⟩ = sndY ξ' := by
    show sndY (i.toPartialMap.hom ⟨ξ, hξmemGf⟩) = sndY ξ'
    rw [hptf]
  have hvalg : g.hom ⟨x, hxg'⟩ = sndY ξ' := by
    have h1 : g.hom ⟨sndX ξ, hxg⟩ = Gf.hom ⟨ξ, hξmemGf⟩ := by
      rw [← PartialMap.fromSpecStalkOfMem_closedPoint g hxg,
        ← PartialMap.fromSpecStalkOfMem_closedPoint Gf hξmemGf, hgerm,
        Scheme.Hom.comp_apply, closedPoint_stalkMap]
    have he : (⟨x, hxg'⟩ : g.domain.toScheme) = ⟨sndX ξ, hxg⟩ := Subtype.ext hxs.symm
    rw [he, h1, hvalGf]
  -- the mutual inverse criterion
  haveI : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := hgover
  haveI : k'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := hkover
  have hgrat' : g.toRationalMap = φ.hom := hgrat.trans hg₀eq
  have hkrat' : k'.toRationalMap = φ.inv := hkrat.trans hk₀eq
  have hy : g.hom ⟨x, hxg'⟩ ∈ k'.domain := by rw [hvalg]; exact hyk
  exact hx (Work.Motivic.isIsoAt_of_mutual_inverse (S := AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
    φ g hgrat' hxg' k' hkrat' hy)


end

end Work.CY3Stab.Prod

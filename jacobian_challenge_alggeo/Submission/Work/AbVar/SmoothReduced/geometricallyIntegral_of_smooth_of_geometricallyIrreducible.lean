import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Smooth + geometrically irreducible ⟹ geometrically integral

A morphism `f : X ⟶ S` of schemes which is smooth and geometrically irreducible is
geometrically integral.  The only mathematical input is that a smooth algebra over a field
is reduced (Mathlib currently lacks this), together with Mathlib's
`GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible`.

The route is:

* `isReduced_of_isStandardSmooth` : a standard smooth algebra over a field is reduced.
  A standard smooth `k`-algebra `S` factors as `k ⟶ k[X₁,…,Xₙ] ⟶ S` with the second map
  étale (`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`).  As `k[X₁,…,Xₙ]` is a domain,
  and `S` is flat (étale) over it, `S` embeds into the reduced ring
  `S ⊗_{k[X]} Frac k[X]` (étale over the field `Frac k[X]`), hence is reduced.

* `isReduced_of_smooth_algebra` : a smooth algebra over a field is reduced.  Smoothness gives
  local standard smoothness (`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`); reducedness
  is local, and we test at a maximal ideal, where one of the standard smooth localizations
  has the form `Aₜ` with `t` a unit.

* `isReduced_of_smooth_to_spec` : a scheme smooth over the spectrum of a field is reduced.
  Reduce to the affine open cover and use `isReduced_of_smooth_algebra` on the section rings.

* `geometricallyReduced_of_smooth'` and the main theorem assemble these.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace Work.AbVar.SmoothReduced

/-- A standard smooth algebra over a field is reduced.

This is proven by factoring the standard smooth structure as an étale extension of a
polynomial algebra and embedding into (the reduced reduction of) the latter's fraction
field. -/
theorem isReduced_of_isStandardSmooth (k S : Type u) [Field k] [CommRing S] [Algebra k S]
    [Algebra.IsStandardSmooth k S] : IsReduced S := by
  obtain ⟨n, g, hgC, hgEtale⟩ :=
    RingHom.IsStandardSmooth.exists_etale_mvPolynomial
      (RingHom.isStandardSmooth_algebraMap.mpr ‹Algebra.IsStandardSmooth k S›)
  let R := MvPolynomial (Fin n) k
  letI : Algebra R S := g.toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra]; exact hgC.symm)
  haveI : Algebra.Etale R S := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]; exact hgEtale
  haveI : IsDomain R := inferInstance
  haveI : Module.Flat R S := inferInstance
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := R) (A := FractionRing R) (B := S)) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R (FractionRing R))
  haveI : IsReduced (TensorProduct R (FractionRing R) S) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing R) (TensorProduct R (FractionRing R) S)
  exact isReduced_of_injective _ hinj

/-- A smooth algebra over a field is reduced. -/
theorem isReduced_of_smooth_algebra (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : IsReduced A := by
  obtain ⟨s, hspan, hsmooth⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth k A
  constructor
  intro x hx
  refine eq_zero_of_localization x (fun J hJ => ?_)
  haveI : J.IsPrime := hJ.isPrime
  obtain ⟨t, ht, htJ⟩ : ∃ t ∈ s, t ∉ J := by
    by_contra h
    push Not at h
    have htop : (⊤ : Ideal A) ≤ J := by
      rw [← hspan]; exact Ideal.span_le.mpr h
    exact hJ.ne_top (top_le_iff.mp htop)
  haveI : Algebra.IsStandardSmooth k (Localization.Away t) := hsmooth t ht
  haveI : IsReduced (Localization.Away t) := isReduced_of_isStandardSmooth k (Localization.Away t)
  have hx0 : (algebraMap A (Localization.Away t)) x = 0 := (hx.map _).eq_zero
  have hunit : IsUnit (algebraMap A (Localization.AtPrime J) t) := by
    have h : t ∈ J.primeCompl := htJ
    exact IsLocalization.map_units (Localization.AtPrime J) ⟨t, h⟩
  have hcomp := IsLocalization.Away.lift_comp (R := A) (S := Localization.Away t)
    (P := Localization.AtPrime J) t hunit
  rw [← hcomp, RingHom.comp_apply, hx0, map_zero]

/-- A ring map from a field whose source ring map is smooth has reduced target. -/
theorem isReduced_of_ringHom_smooth (k A : Type u) [Field k] [CommRing A] (f : k →+* A)
    (hf : RingHom.Smooth f) : IsReduced A := by
  letI : Algebra k A := f.toAlgebra
  haveI : Algebra.Smooth k A := hf
  exact isReduced_of_smooth_algebra k A

open CategoryTheory AlgebraicGeometry in
/-- A scheme smooth over the spectrum of a field is reduced. -/
theorem isReduced_of_smooth_to_spec (K : Type u) [Field K] (Z : Scheme.{u})
    (g : Z ⟶ Spec (.of K)) [Smooth g] : IsReduced Z := by
  haveI : MorphismProperty.RespectsLeft @Smooth @IsOpenImmersion :=
    (inferInstance : MorphismProperty.Respects @Smooth @IsOpenImmersion).toRespectsLeft
  refine @IsReduced.of_openCover Z Z.affineCover ?_
  intro i
  have hsm : Smooth (Z.affineCover.f i ≫ g) :=
    MorphismProperty.RespectsLeft.precomp (Z.affineCover.f i) (Z.affineCover.map_prop i) g ‹Smooth g›
  haveI : IsAffine (Z.affineCover.X i) := inferInstance
  haveI : IsAffine (Spec (.of K)) := inferInstance
  have hφ : RingHom.Smooth (((Z.affineCover.f i ≫ g).appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (HasRingHomProperty.appTop @Smooth (Z.affineCover.f i ≫ g) hsm)
  haveI : IsReduced Γ(Z.affineCover.X i, ⊤) :=
    isReduced_of_ringHom_smooth K Γ(Z.affineCover.X i, ⊤) _ hφ
  exact isReduced_of_isAffine_isReduced _

/-- A smooth morphism of schemes is geometrically reduced. -/
theorem geometricallyReduced_of_smooth' {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] :
    AlgebraicGeometry.GeometricallyReduced f := by
  refine ⟨fun {K} _ y {Z} fst snd h => ?_⟩
  haveI : AlgebraicGeometry.Smooth snd := by
    apply CategoryTheory.MorphismProperty.of_isPullback
      (P := @AlgebraicGeometry.Smooth) h
    exact ‹AlgebraicGeometry.Smooth f›
  exact isReduced_of_smooth_to_spec K Z snd

/-- A smooth, geometrically irreducible morphism of schemes is geometrically integral. -/
theorem geometricallyIntegral_of_smooth_of_geometricallyIrreducible
    {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] [AlgebraicGeometry.GeometricallyIrreducible f] :
    AlgebraicGeometry.GeometricallyIntegral f := by
  haveI : AlgebraicGeometry.GeometricallyReduced f := geometricallyReduced_of_smooth' f
  exact AlgebraicGeometry.GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

end Work.AbVar.SmoothReduced

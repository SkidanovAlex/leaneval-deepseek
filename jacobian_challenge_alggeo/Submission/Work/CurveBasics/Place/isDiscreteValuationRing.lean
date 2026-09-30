/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local ring of a smooth curve at a closed point is a discrete valuation ring

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k` (the bundled
`Work.CurveBasics.Curve`) and `Q : C.Place` a closed point.  This file proves that the local
ring `𝒪_{C,Q}` is a discrete valuation ring.

The mathematical content is the following chain.

* The sheaf of relative differentials of a standard smooth algebra of relative dimension one
  over a field is free of rank one; equivalently, a chart of the curve over `k` is, locally,
  *étale* over the polynomial ring in one variable
  (`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`).
* `k[X]` is a principal ideal ring, so the maximal ideal of `k[X]` localized at any prime is
  principal.
* An étale (= unramified) localization of a principal ideal ring has principal maximal ideal:
  `Algebra.FormallyUnramified.map_maximalIdeal` says that the maximal ideal of the target is
  the extension of the maximal ideal of the source.
* The local ring `𝒪_{C,Q}` is a Noetherian local domain of Krull dimension one which is not a
  field, so having principal maximal ideal makes it a discrete valuation ring
  (`IsDiscreteValuationRing.TFAE`).

The bridge between the algebraic statements and the curve is the chart lemma
`Work.CurveBasics.Place.exists_standardSmooth_chart` (a smooth morphism of relative dimension
one is, at every point, standard smooth of relative dimension one, hence étale over `k[X]`).
-/
import Mathlib
import Submission.Work.CurveBasics.Place.Coheight

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

/-- A ring homomorphism carries principal ideals to principal ideals. -/
theorem isPrincipal_map_of_isPrincipal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} (hI : I.IsPrincipal) : (Ideal.map f I).IsPrincipal := by
  obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal I
  exact ⟨f x, by rw [hx, Ideal.map_span, Set.image_singleton]⟩

/-- The polynomial ring in one variable over a field is a principal ideal ring. -/
instance isPrincipalIdealRing_mvPolynomial_fin_one (k : Type*) [Field k] :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) k) :=
  IsPrincipalIdealRing.of_surjective (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.toRingEquiv
    (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.surjective

/-- **The algebraic heart of the statement that the local ring of a smooth curve at a closed
point is a discrete valuation ring.**

Let `k` be a field, `A` a domain and `ψ : k →+* A` a standard smooth ring homomorphism of
relative dimension one (the algebraic shadow of a standard smooth chart of a curve).  Then the
maximal ideal of `A` localized at any maximal ideal `p` is principal.

Indeed, by `RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` the ring `A`
is étale over the polynomial ring in one variable `R = k[X]`.  Let `q = p ∩ R`.  Since `A` is
formally unramified over `R`, the localized map `R_q → A_p` is formally unramified
(`Algebra.IsUnramifiedAt`, `Localization.AtPrime.algebraOfLiesOver`), so
`Algebra.FormallyUnramified.map_maximalIdeal` shows that the maximal ideal of `A_p` is the
extension of the maximal ideal of `R_q`.  That maximal ideal is principal because `R = k[X]` is
a principal ideal ring. -/
theorem isPrincipal_maximalIdeal_of_isStandardSmooth_relDim_one {k A : Type*} [Field k]
    [CommRing A] [IsDomain A] {ψ : k →+* A}
    (hss : ψ.IsStandardSmoothOfRelativeDimension 1) (p : Ideal A) [p.IsMaximal] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).IsPrincipal := by
  obtain ⟨g, _hgc, hge⟩ := hss.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin 1) k) A := g.toAlgebra
  haveI : @Algebra.Etale (MvPolynomial (Fin 1) k) A _ _ g.toAlgebra := hge.toAlgebra
  have key : Algebra.FormallyUnramified (MvPolynomial (Fin 1) k) A := inferInstance
  have hU : Algebra.IsUnramifiedAt (MvPolynomial (Fin 1) k) p :=
    (Algebra.formallyUnramified_iff_forall.mp key) ⟨p, inferInstance⟩
  let q : Ideal (MvPolynomial (Fin 1) k) := p.under (MvPolynomial (Fin 1) k)
  haveI hq : q.IsPrime := inferInstance
  haveI hover : p.LiesOver q := Ideal.over_under p
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime p) :=
    Localization.AtPrime.algebraOfLiesOver q p
  haveI : Algebra.FormallyUnramified (Localization.AtPrime q) (Localization.AtPrime p) :=
    inferInstance
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin 1) k) (Localization.AtPrime p) := inferInstance
  haveI : Algebra.EssFiniteType (Localization.AtPrime q) (Localization.AtPrime p) :=
    Algebra.EssFiniteType.of_comp (MvPolynomial (Fin 1) k) (Localization.AtPrime q)
      (Localization.AtPrime p)
  have hmap := Algebra.FormallyUnramified.map_maximalIdeal
    (R := Localization.AtPrime q) (S := Localization.AtPrime p)
  have h1 : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).IsPrincipal := by
    have := isPrincipal_map_of_isPrincipal
      (algebraMap (MvPolynomial (Fin 1) k) (Localization.AtPrime q))
      (IsPrincipalIdealRing.principal q)
    rwa [Localization.AtPrime.map_eq_maximalIdeal] at this
  rw [← hmap]
  exact isPrincipal_map_of_isPrincipal _ h1

end Work.CurveBasics

namespace Work.CurveBasics.Place

open Work.CurveBasics in
/-- Assemble the discrete valuation ring statement from a standard smooth chart of the curve at
`Q`: `V` is an affine open neighbourhood of `Q.point`, `ψ` exhibits `Γ(C.left, V)` as standard
smooth of relative dimension one over `k`, `e` identifies `Γ(C.left, V)` localized at the prime
of `Q.point` with the local ring `𝒪_{C,Q}`, and that prime is maximal. -/
theorem isDiscreteValuationRing_of_chart {k : Type*} [Field k] {C : Curve k} (Q : C.Place)
    (V : C.left.Opens) (hV : IsAffineOpen V) (hxV : Q.point ∈ V) (ψ : k →+* Γ(C.left, V))
    (e : Localization.AtPrime (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal ≃+*
      C.left.presheaf.stalk Q.point)
    (hss : ψ.IsStandardSmoothOfRelativeDimension 1)
    (hmax : (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal.IsMaximal) :
    IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) := by
  haveI : Nonempty V := ⟨⟨Q.point, hxV⟩⟩
  haveI hdom : IsDomain Γ(C.left, V) := IsIntegral.component_integral V
  haveI hnoeth : IsNoetherianRing Γ(C.left, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI hprime : (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal.IsPrime := hmax.isPrime
  have hprin : (IsLocalRing.maximalIdeal
      (Localization.AtPrime (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal)).IsPrincipal :=
    isPrincipal_maximalIdeal_of_isStandardSmooth_relDim_one hss _
  have hdim : ringKrullDim (Localization.AtPrime (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e, Q.ringKrullDim_localRing]
  have hnf : ¬ IsField (Localization.AtPrime (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal) := by
    intro hf
    letI := hf.toField
    have h0 : ringKrullDim (Localization.AtPrime (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal) = 0 :=
      ringKrullDim_eq_zero_of_field _
    rw [h0] at hdim
    exact zero_ne_one hdim
  haveI : IsDiscreteValuationRing
      (Localization.AtPrime (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr hprin
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

open Work.CurveBasics in
theorem isDiscreteValuationRing {k : Type*} [Field k] {C : Curve k} (Q : C.Place) :
    IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) := by
  -- a chart of the curve at `Q`: an affine open `V ⊆ C` and, on it, a standard smooth
  -- `k`-algebra of relative dimension one.
  obtain ⟨U, _hU, V, hV, hxV, hle, hss⟩ :=
    C.smooth.exists_isStandardSmoothOfRelativeDimension Q.point
  have hxU : C.hom Q.point ∈ U := hle hxV
  -- `Spec k` is a single point, so `U = ⊤`
  have hUt : U = ⊤ := by
    haveI : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
    ext y
    constructor
    · intro _; trivial
    · intro _
      rw [Subsingleton.elim y (C.hom Q.point)]
      exact hxU
  subst hUt
  -- the `k`-algebra structure on the chart,  `k ≅ Γ(Spec k, ⊤)`
  letI : Algebra Γ(C.left, V) (C.left.presheaf.stalk Q.point) :=
    (C.left.presheaf.germ V Q.point hxV).hom.toAlgebra
  haveI hloc : IsLocalization.AtPrime (C.left.presheaf.stalk Q.point)
      (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨Q.point, hxV⟩
  refine isDiscreteValuationRing_of_chart Q V hV hxV
    ((C.hom.appLE ⊤ V hle).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm).toRingHom)
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨Q.point, hxV⟩).asIdeal)
      (C.left.presheaf.stalk Q.point)).toRingEquiv ?_ ?_
  · exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)).2
      (C.hom.appLE ⊤ V hle).hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm) hss
  · exact hV.primeIdealOf_isMaximal_of_isClosed ⟨Q.point, hxV⟩ Q.isClosed

end Work.CurveBasics.Place

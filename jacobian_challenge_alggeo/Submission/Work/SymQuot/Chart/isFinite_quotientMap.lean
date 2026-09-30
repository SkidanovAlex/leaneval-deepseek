/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quotient map `X ⟶ X/Γ` is finite (area SY)

Let `Γ` be a finite group acting on a scheme `X` and let `D : Work.SymQuot.QuotientData Γ X` be
the data of a `Γ`-invariant affine open cover of `X` (from which the quotient `D.Quotient` and the
quotient map `D.quotientMap : X ⟶ D.Quotient` are constructed).

**Main result.** If for every chart `U` of the cover the local model of the quotient, the chart map
`chartMap U : U ⟶ Spec Γ(X,U)^Γ`, is a *finite* morphism, then the quotient map itself is finite:

`Work.SymQuot.Chart.isFinite_quotientMap : IsFinite D.quotientMap`.

The hypothesis is exactly the local finiteness statement that is supplied by
`Work.SymQuot.Sym.isFinite_chartMap` (under the standing assumptions that `X` is locally of finite
type over a field and the action is by automorphisms over the field).  So this file reduces the
global finiteness of `X ⟶ X/Γ` to its local model.

The argument is the standard "Zariski local on the target" reduction, and is the verbatim analogue
of the proof that the quotient map is integral
(`Work.SymQuot.Chart.quotientMap_isIntegralHom`): the charts `chartι U : chart U ⟶ X/Γ` cover the
quotient, and base changing the quotient map along the open immersion `chartι U` recovers the chart
map `chartMap U` (the square is cartesian, see
`Work.SymQuot.QuotientData.isPullback_chartMap_quotientMap`).  Concretely, for a point `x` of the
quotient lying in the chart of `U`, the restriction of the quotient map to the open
`(chartι U).opensRange` is, after the identifications

* `D.quotientMap ⁻¹ᵁ (chartι U).opensRange = U.1`
  (`Work.SymQuot.QuotientData.quotientMap_preimage_opensRange_chartι`), and
* `chart U ≅ (chartι U).opensRange`,

the chart map `chartMap U`, hence finite by hypothesis.
-/
import Mathlib
import Submission.Work.SymQuot.QuotientHom
import Submission.Work.SymQuot.Chart.quotientMap_isIntegralHom

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Chart

/-- **The quotient map `X ⟶ X/Γ` is finite.**  If every chart map `chartMap U` is finite, then so
is `D.quotientMap`: finiteness of morphisms is Zariski local on the target, the charts of the
quotient form an open cover, and on each chart the quotient map is the chart map. -/
theorem isFinite_quotientMap {Γ : Type u} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme.{u}}
    (D : Work.SymQuot.QuotientData Γ X)
    (h : ∀ U : D.Chart, AlgebraicGeometry.IsFinite (D.action.chartMap U.1 U.2.2)) :
    AlgebraicGeometry.IsFinite D.quotientMap := by
  -- `@IsFinite` is a `HasAffineProperty` and hence Zariski local at the target.  Instance search
  -- does not pick up the (anonymous, `outParam`-valued) `HasAffineProperty` instance on its own,
  -- so the locality instance is provided explicitly; the shape is the same as for
  -- `IsIntegralHom` in `Work.SymQuot.Chart.quotientMap_isIntegralHom`.
  letI : IsZariskiLocalAtTarget (@AlgebraicGeometry.IsFinite) :=
    @AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget _
      (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
      AlgebraicGeometry.IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
  -- it suffices to find, for every point of the quotient, an open neighbourhood on which the
  -- quotient map is finite; take the chart containing the point
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := @AlgebraicGeometry.IsFinite) (f := D.quotientMap) fun x => ?_
  obtain ⟨U, y, hy⟩ := D.chartι_jointly_surjective x
  refine ⟨(D.chartι U).opensRange, ?_, ?_⟩
  · -- the point `x` lies in the chart of `U`
    rw [Scheme.Hom.mem_opensRange]
    exact ⟨y, hy⟩
  · -- on the chart of `U` the quotient map is the chart map, up to isomorphism
    have hK1 : D.quotientMap ⁻¹ᵁ (D.chartι U).opensRange = U.1 :=
      Work.SymQuot.QuotientData.quotientMap_preimage_opensRange_chartι D U
    -- the identification of `V := (chartι U).opensRange` with `chart U`
    have hrange : Set.range (D.chartι U) = Set.range ((D.chartι U).opensRange).ι := by
      show Set.range (D.chartι U) = ((((D.chartι U).opensRange).ι).opensRange : Set D.Quotient)
      rw [Scheme.Opens.opensRange_ι]
      rfl
    set e' : D.chart U ≅ ((D.chartι U).opensRange).toScheme :=
      IsOpenImmersion.isoOfRangeEq (D.chartι U) ((D.chartι U).opensRange).ι hrange with he'def
    have he'fac : e'.hom ≫ ((D.chartι U).opensRange).ι = D.chartι U := by
      rw [he'def]
      exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    -- the transport of the source of the restriction along `q ⁻¹ᵁ V = U`
    set γ : (D.quotientMap ⁻¹ᵁ (D.chartι U).opensRange).toScheme ≅ U.1.toScheme :=
      X.isoOfEq hK1 with hγdef
    have hγ : γ.inv ≫ (D.quotientMap ⁻¹ᵁ (D.chartι U).opensRange).ι = U.1.ι := by
      rw [hγdef]
      exact Scheme.isoOfEq_inv_ι X hK1
    -- the restriction of the quotient map to the chart is the chart map, up to these isomorphisms
    have key : γ.inv ≫ (D.quotientMap ∣_ (D.chartι U).opensRange) =
        D.action.chartMap U.1 U.2.2 ≫ e'.hom := by
      apply (cancel_mono ((D.chartι U).opensRange).ι).mp
      calc (γ.inv ≫ (D.quotientMap ∣_ (D.chartι U).opensRange)) ≫ ((D.chartι U).opensRange).ι
          = γ.inv ≫ ((D.quotientMap ∣_ (D.chartι U).opensRange) ≫
              ((D.chartι U).opensRange).ι) := Category.assoc ..
        _ = γ.inv ≫ ((D.quotientMap ⁻¹ᵁ (D.chartι U).opensRange).ι ≫ D.quotientMap) := by
              rw [morphismRestrict_ι]
        _ = (γ.inv ≫ (D.quotientMap ⁻¹ᵁ (D.chartι U).opensRange).ι) ≫ D.quotientMap :=
            (Category.assoc ..).symm
        _ = U.1.ι ≫ D.quotientMap := by rw [hγ]
        _ = D.action.chartMap U.1 U.2.2 ≫ D.chartι U := D.quotientMap_chartι U
        _ = D.action.chartMap U.1 U.2.2 ≫ (e'.hom ≫ ((D.chartι U).opensRange).ι) := by rw [he'fac]
        _ = (D.action.chartMap U.1 U.2.2 ≫ e'.hom) ≫ ((D.chartι U).opensRange).ι :=
            (Category.assoc ..).symm
    -- the chart map is finite by hypothesis, and `e'` is an isomorphism
    haveI : AlgebraicGeometry.IsFinite (D.action.chartMap U.1 U.2.2) := h U
    haveI h2 : AlgebraicGeometry.IsFinite
        (γ.inv ≫ (D.quotientMap ∣_ (D.chartι U).opensRange)) := by
      rw [key]
      exact inferInstance
    have h3 : (D.quotientMap ∣_ (D.chartι U).opensRange) =
        γ.hom ≫ (γ.inv ≫ (D.quotientMap ∣_ (D.chartι U).opensRange)) := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h3]
    exact inferInstance

end Work.SymQuot.Chart

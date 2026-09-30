/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quotient map `X ⟶ X/Γ` is integral (area SY)

For a scheme `X` with an action of a finite group `Γ` and a `Γ`-invariant affine open cover
(`Work.SymQuot.QuotientData`), the quotient map `D.quotientMap : X ⟶ D.Quotient` is *integral*.

The proof is local on the target.  The quotient is the locally directed colimit of the chart
diagram `U ↦ Spec Γ(X,U)^Γ`, and over the chart `U` the quotient map is the chart map
`chartMap U : U ⟶ Spec Γ(X,U)^Γ`, which is integral because `Γ(X,U)` is integral over its
invariant subring `Γ(X,U)^Γ` for a finite group (`Work.SymQuot.Invariants.fixedPoints_isIntegral`).

The comparison between the quotient map and the chart maps is made precise by two lemmas proved
below (both of independent interest):

* `Work.SymQuot.QuotientData.quotientMap_preimage_opensRange_chartι`: the preimage of the range of
  a chart inclusion is exactly that chart.  It uses that the fibres of the quotient map are the
  `Γ`-orbits (`Work.SymQuot.Chart.quotientMap_fiber_orbit`).
* `Work.SymQuot.QuotientData.isPullback_chartMap_quotientMap`: the square
  ```
      U  --chartMap U-->  chart U
      |                      |
    U.ι                  chartι U
      v                      v
      X --quotientMap-->  X/Γ
  ```
  is cartesian, so that base changing the quotient map along the open immersion `chartι U`
  recovers the chart map `chartMap U`.

## Main result

* `Work.SymQuot.Chart.quotientMap_isIntegralHom`: `D.quotientMap` is integral.
-/
import Mathlib
import Submission.Work.SymQuot.QuotientHom
import Submission.Work.SymQuot.QuotientData
import Submission.Work.SymQuot.Invariants.fixedPoints_isIntegral
import Submission.Work.SymQuot.Chart.chartMap_isIntegralHom
import Submission.Work.SymQuot.Chart.quotientMap_fiber_orbit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

namespace QuotientData

variable {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}}

/-- The preimage under the quotient map of the range of the chart inclusion of a chart `U` is
exactly `U`: a point of `X` is mapped into the chart of `U` in the quotient if and only if it lies
in `U` itself.  (One inclusion is immediate from `quotientMap_chartι`, the other uses that the
fibres of the quotient map are the `Γ`-orbits, see
`Work.SymQuot.Chart.quotientMap_fiber_orbit`.) -/
theorem quotientMap_preimage_opensRange_chartι (D : QuotientData Γ X) (U : D.Chart) :
    D.quotientMap ⁻¹ᵁ (D.chartι U).opensRange = U.1 := by
  refine le_antisymm ?_ ?_
  · -- a point mapping into the chart of `U` lies in the `Γ`-orbit of a point of `U`
    intro x hx
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange] at hx
    obtain ⟨c, hc⟩ := hx
    obtain ⟨w, hw⟩ := Work.SymQuot.Chart.chartMap_surjective D.action U.2.1 U.2.2 c
    have hq : D.quotientMap (U.1.ι w) = D.chartι U c := by
      have h := congrFun (congrArg (fun φ : U.1.toScheme ⟶ D.Quotient => ⇑φ)
        (D.quotientMap_chartι U)) w
      simp only [Scheme.Hom.comp_apply] at h
      rw [hw] at h
      exact h
    have hqx : D.quotientMap x = D.quotientMap (U.1.ι w) := hc.symm.trans hq.symm
    obtain ⟨g, hg⟩ := Work.SymQuot.Chart.quotientMap_fiber_orbit D hqx
    exact (U.2.2.mem_iff g x).mp (by rw [hg, Scheme.Opens.ι_apply U.1 w]; exact w.2)
  · -- `U` maps into the range of the chart map because that map is surjective
    intro x hx
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
    refine ⟨D.action.chartMap U.1 U.2.2 (⟨x, hx⟩ : U.1.toScheme), ?_⟩
    have h1 : D.quotientMap (U.1.ι (⟨x, hx⟩ : U.1.toScheme)) =
        D.chartι U (D.action.chartMap U.1 U.2.2 (⟨x, hx⟩ : U.1.toScheme)) := by
      rw [← Scheme.Hom.comp_apply (f := U.1.ι) (g := D.quotientMap)
            (x := (⟨x, hx⟩ : U.1.toScheme)),
          ← Scheme.Hom.comp_apply (f := D.action.chartMap U.1 U.2.2) (g := D.chartι U)
            (x := (⟨x, hx⟩ : U.1.toScheme)),
          D.quotientMap_chartι U]
    rw [← h1, Scheme.Opens.ι_apply U.1 (⟨x, hx⟩ : U.1.toScheme)]

/-- The square
```
    U  --chartMap U-->  chart U
    |                      |
  U.ι                  chartι U
    v                      v
    X --quotientMap-->  X/Γ
```
is cartesian: base changing the quotient map along the open immersion `chartι U` recovers the
chart map `chartMap U`, which is the local model of the quotient map. -/
theorem isPullback_chartMap_quotientMap (D : QuotientData Γ X) (U : D.Chart) :
    IsPullback (D.action.chartMap U.1 U.2.2) U.1.ι (D.chartι U) D.quotientMap :=
  IsOpenImmersion.isPullback (D.action.chartMap U.1 U.2.2) U.1.ι (D.chartι U) D.quotientMap
    (D.quotientMap_chartι U)
    ((quotientMap_preimage_opensRange_chartι D U).trans (Scheme.Opens.opensRange_ι U.1).symm)

end QuotientData

namespace Chart

/-- **The quotient map `X ⟶ X/Γ` is integral.**  It is locally on the target the chart map
`U ⟶ Spec Γ(X,U)^Γ`, which is integral because `Γ(X,U)` is integral over its invariants
`Γ(X,U)^Γ` for a finite group `Γ`. -/
theorem quotientMap_isIntegralHom {Γ : Type*} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme}
    (D : Work.SymQuot.QuotientData Γ X) :
    AlgebraicGeometry.IsIntegralHom D.quotientMap := by
  -- `@IsIntegralHom` is not found by instance search (its binders are explicit in the declaration,
  -- while `MorphismProperty` uses implicit binders), so the locality instance is provided by hand.
  letI : IsZariskiLocalAtTarget (@AlgebraicGeometry.IsIntegralHom) :=
    @AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget _ _
      AlgebraicGeometry.IsIntegralHom.hasAffineProperty
  -- it suffices to check integrality on the open cover of `X/Γ` given by the charts
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := @AlgebraicGeometry.IsIntegralHom) (f := D.quotientMap) fun x => ?_
  obtain ⟨U, y, hy⟩ := D.chartι_jointly_surjective x
  refine ⟨(D.chartι U).opensRange, ?_, ?_⟩
  · rw [Scheme.Hom.mem_opensRange]
    exact ⟨y, hy⟩
  · -- on the chart `U` the quotient map is the chart map, up to isomorphism
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
    haveI : AlgebraicGeometry.IsIntegralHom (D.action.chartMap U.1 U.2.2) :=
      chartMap_isIntegralHom D.action U.2.1 U.2.2
    haveI h2 : AlgebraicGeometry.IsIntegralHom
        (γ.inv ≫ (D.quotientMap ∣_ (D.chartι U).opensRange)) := by
      rw [key]
      exact inferInstance
    have h3 : (D.quotientMap ∣_ (D.chartι U).opensRange) =
        γ.hom ≫ (γ.inv ≫ (D.quotientMap ∣_ (D.chartι U).opensRange)) := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h3]
    exact inferInstance

end Chart

end Work.SymQuot

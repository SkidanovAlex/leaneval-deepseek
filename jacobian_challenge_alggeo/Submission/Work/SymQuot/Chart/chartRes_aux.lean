/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary facts for the chart restriction maps of a finite group quotient (area SY)

This file collects the geometric and ring theoretic facts underlying the proof that the
restriction map between charts `chart V ⟶ chart U` of `G`-invariant affine opens `V ≤ U`
of a scheme `X` with an action of a finite group `G` is an open immersion
(`Work.SymQuot.Chart.chartRes_isOpenImmersion_alt`).

The main ingredients here are

* `isOpenImmersion_specMap_restrictSections`: the morphism `Spec Γ(X,V) ⟶ Spec Γ(X,U)`
  induced by the restriction of sections along `V ≤ U` is an open immersion;
* `isInvariantOpen_basicOpen`: the basic open of a `G`-fixed section is a `G`-invariant open;
* `chartRes_isOpenImmersion_basicOpen`: the restriction map between charts is an open
  immersion when the smaller chart is the chart of a basic open of an invariant section
  (the "distinguished" case).
-/
import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Invariants.fixedPoints_isLocalization_away

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SymQuot.Chart

variable {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}

/-- For affine opens `V ≤ U` of a scheme `X`, the morphism of spectra
`Spec Γ(X,V) ⟶ Spec Γ(X,U)` induced by the restriction of sections is an open immersion: it is,
up to the canonical identifications `U ≅ Spec Γ(X,U)` and `V ≅ Spec Γ(X,V)`, the inclusion
`V ⟶ U`. -/
theorem isOpenImmersion_specMap_restrictSections {V U : X.Opens}
    (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.restrictSections V U hVU))) := by
  have hnat := Scheme.Opens.toSpecΓ_SpecMap_presheaf_map V U hVU
  have h2 : Spec.map (X.presheaf.map (homOfLE hVU).op)
      = hV.isoSpec.inv ≫ X.homOfLE hVU ≫ hU.isoSpec.hom := by
    rw [IsAffineOpen.isoSpec_hom, ← hnat, ← Category.assoc, IsAffineOpen.isoSpec_inv_toSpecΓ,
      Category.id_comp]
  show IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE hVU).op))
  rw [h2]
  infer_instance

/-- The morphism `app U` of an automorphism `A.hom g` of `X` with invariant open `U` is the
action on the sections over `U`, transported along the identification `A.hom g ⁻¹ᵁ U = U`. -/
lemma app_eq_sectionHom (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hUi : A.IsInvariantOpen U) (g : G) (h : Γ(X,U)) :
    X.presheaf.map (eqToHom (hUi g).symm).op ((A.hom g).app U h)
      = Work.SymQuot.GAction.sectionHom A U hUi g h := by
  have h1 : (eqToHom (hUi g).symm : U ⟶ A.hom g ⁻¹ᵁ U)
      = homOfLE (le_of_eq (hUi g).symm) := Subsingleton.elim _ _
  simp only [Work.SymQuot.GAction.sectionHom_apply, Scheme.Hom.appLE,
    ConcreteCategory.comp_apply, h1]

/-- The basic open of a section fixed by the action on an invariant open is an invariant open. -/
lemma isInvariantOpen_basicOpen (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hUi : A.IsInvariantOpen U) (h : Γ(X,U))
    (hh : ∀ g : G, Work.SymQuot.GAction.sectionHom A U hUi g h = h) :
    A.IsInvariantOpen (X.basicOpen h) := by
  intro g
  rw [Scheme.preimage_basicOpen,
    ← Scheme.basicOpen_res_eq (X := X) (f := (A.hom g).app U h)
      (i := (eqToHom (hUi g).symm).op),
    app_eq_sectionHom A hUi g h, hh g]

/-- Restricting a section and then taking a basic open does not change the basic open, provided
the basic open is contained in the smaller open. -/
lemma basicOpen_restrictSections_eq {V U : X.Opens} (hVU : V ≤ U) (h : Γ(X,U))
    (hle : X.basicOpen h ≤ V) :
    X.basicOpen (Work.SymQuot.GAction.restrictSections V U hVU h) = X.basicOpen h := by
  rw [Work.SymQuot.GAction.restrictSections, Scheme.basicOpen_res]
  exact inf_eq_right.mpr hle

/-- **The distinguished case.**  If `h` is a section over an invariant affine open `U` which is
fixed by the action, then the restriction map `chart (X.basicOpen h) ⟶ chart U` between the charts
of the (invariant) basic open `X.basicOpen h` and of `U` is an open immersion. -/
theorem chartRes_isOpenImmersion_basicOpen (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hU : IsAffineOpen U) (hUi : A.IsInvariantOpen U) (h : Γ(X,U))
    (hh : ∀ g : G, Work.SymQuot.GAction.sectionHom A U hUi g h = h)
    (hW : A.IsInvariantOpen (X.basicOpen h)) :
    IsOpenImmersion (Work.SymQuot.GAction.chartRes A (X.basicOpen h) U
      (X.basicOpen_le h) hUi hW) := by
  letI : MulSemiringAction G Γ(X,U) := A.sectionMulSemiringAction U hUi
  letI : MulSemiringAction G Γ(X, X.basicOpen h) := A.sectionMulSemiringAction (X.basicOpen h) hW
  haveI hloc : IsLocalization.Away h Γ(X, X.basicOpen h) := hU.isLocalization_basicOpen h
  have hmem : h ∈ FixedPoints.subring Γ(X,U) G := fun g => hh g⁻¹
  have hcompat : ∀ (g : G) (r : Γ(X,U)),
      algebraMap Γ(X,U) Γ(X, X.basicOpen h) (g • r)
        = g • algebraMap Γ(X,U) Γ(X, X.basicOpen h) r := by
    intro g r
    change Work.SymQuot.GAction.restrictSections (X.basicOpen h) U (X.basicOpen_le h)
        (Work.SymQuot.GAction.sectionHom A U hUi g⁻¹ r)
      = Work.SymQuot.GAction.sectionHom A (X.basicOpen h) hW g⁻¹
        (Work.SymQuot.GAction.restrictSections (X.basicOpen h) U (X.basicOpen_le h) r)
    have h2 := congr($(Work.SymQuot.GAction.restrictSections_sectionHom A (X.basicOpen h) U
      (X.basicOpen_le h) hUi hW g⁻¹) r)
    simpa [RingHom.comp_apply] using h2
  letI : Algebra (FixedPoints.subring Γ(X,U) G) (FixedPoints.subring Γ(X, X.basicOpen h) G) :=
    RingHom.toAlgebra (Work.SymQuot.fixedPointsMap hcompat)
  haveI hloc' : IsLocalization.Away (⟨h, hmem⟩ : FixedPoints.subring Γ(X,U) G)
      (FixedPoints.subring Γ(X, X.basicOpen h) G) :=
    Work.SymQuot.Invariants.fixedPoints_isLocalization_away hcompat h hmem
  show IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (Work.SymQuot.GAction.invariantsRes A (X.basicOpen h) U (X.basicOpen_le h) hUi hW)))
  rw [show Work.SymQuot.GAction.invariantsRes A (X.basicOpen h) U (X.basicOpen_le h) hUi hW
      = algebraMap (FixedPoints.subring Γ(X,U) G) (FixedPoints.subring Γ(X, X.basicOpen h) G)
      from RingHom.ext fun s => Subtype.ext (by
        rw [Work.SymQuot.GAction.invariantsRes_apply]
        exact (Work.SymQuot.fixedPointsMap_coe hcompat s).symm)]
  exact IsOpenImmersion.of_isLocalization (⟨h, hmem⟩ : FixedPoints.subring Γ(X,U) G)

/-- **The basic open of a fixed section inside an invariant affine open.**  If `h` is a section
over an invariant affine open `U` fixed by the action of `G`, and if its basic open `X.basicOpen h`
is contained in a `G`-invariant affine open `V ≤ U`, then the restriction map of charts
`chart (X.basicOpen h) ⟶ chart V` is an open immersion. -/
lemma chartRes_isOpenImmersion_basicOpen_le (A : Work.SymQuot.GAction G X) {V U : X.Opens}
    (hVU : V ≤ U) (hV : IsAffineOpen V) (hVi : A.IsInvariantOpen V) (hUi : A.IsInvariantOpen U)
    (h : Γ(X,U)) (hh : ∀ g : G, Work.SymQuot.GAction.sectionHom A U hUi g h = h)
    (hle : X.basicOpen h ≤ V) (hW : A.IsInvariantOpen (X.basicOpen h)) :
    IsOpenImmersion (Work.SymQuot.GAction.chartRes A (X.basicOpen h) V hle hVi hW) := by
  letI : MulSemiringAction G Γ(X,V) := A.sectionMulSemiringAction V hVi
  letI : MulSemiringAction G Γ(X, X.basicOpen h) := A.sectionMulSemiringAction (X.basicOpen h) hW
  set g : Γ(X,V) := Work.SymQuot.GAction.restrictSections V U hVU h with hg_def
  have he : X.basicOpen g = X.basicOpen h := by
    rw [hg_def]; exact basicOpen_restrictSections_eq hVU h hle
  have hg : ∀ γ : G, Work.SymQuot.GAction.sectionHom A V hVi γ g = g := by
    intro γ
    rw [hg_def]
    have h2 := congr($(Work.SymQuot.GAction.restrictSections_sectionHom A V U hVU hUi hVi γ) h)
    simp only [RingHom.comp_apply] at h2
    rw [hh γ] at h2
    exact h2.symm
  have hmem : g ∈ FixedPoints.subring Γ(X,V) G := fun γ => hg γ⁻¹
  let e : Γ(X, X.basicOpen g) ≃+* Γ(X, X.basicOpen h) :=
    (X.presheaf.mapIso (eqToIso he.symm).op).commRingCatIsoToRingEquiv
  have halg : (e.toRingHom.comp (algebraMap Γ(X,V) Γ(X, X.basicOpen g)))
      = (X.presheaf.map (homOfLE hle).op).hom := by
    apply RingHom.ext
    intro r
    show (X.presheaf.map (eqToHom he.symm).op).hom
        ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom r)
      = (X.presheaf.map (homOfLE hle).op).hom r
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← CategoryTheory.op_comp,
      Subsingleton.elim (eqToHom he.symm ≫ homOfLE (X.basicOpen_le g) : X.basicOpen h ⟶ V)
        (homOfLE hle)]
  letI : Algebra Γ(X,V) Γ(X, X.basicOpen h) :=
    RingHom.toAlgebra (e.toRingHom.comp (algebraMap Γ(X,V) Γ(X, X.basicOpen g)))
  letI : Algebra Γ(X, X.basicOpen g) Γ(X, X.basicOpen h) := RingHom.toAlgebra e.toRingHom
  haveI hloc : IsLocalization.Away g Γ(X, X.basicOpen h) := by
    have hcan : IsLocalization.Away g Γ(X, X.basicOpen g) := hV.isLocalization_basicOpen g
    have hiff := (IsLocalization.isLocalization_iff_of_ringEquiv (M := Submonoid.powers g) e).mp hcan
    convert hiff using 2
  have hcompat : ∀ (γ : G) (r : Γ(X,V)),
      algebraMap Γ(X,V) Γ(X, X.basicOpen h) (γ • r)
        = γ • algebraMap Γ(X,V) Γ(X, X.basicOpen h) r := by
    intro γ r
    rw [show algebraMap Γ(X,V) Γ(X, X.basicOpen h)
        = (X.presheaf.map (homOfLE hle).op).hom from halg]
    change Work.SymQuot.GAction.restrictSections (X.basicOpen h) V hle
        (Work.SymQuot.GAction.sectionHom A V hVi γ⁻¹ r)
      = Work.SymQuot.GAction.sectionHom A (X.basicOpen h) hW γ⁻¹
        (Work.SymQuot.GAction.restrictSections (X.basicOpen h) V hle r)
    have h2 := congr($(Work.SymQuot.GAction.restrictSections_sectionHom A (X.basicOpen h) V
      hle hVi hW γ⁻¹) r)
    simpa [RingHom.comp_apply] using h2
  letI : Algebra (FixedPoints.subring Γ(X,V) G) (FixedPoints.subring Γ(X, X.basicOpen h) G) :=
    RingHom.toAlgebra (Work.SymQuot.fixedPointsMap hcompat)
  haveI hloc' : IsLocalization.Away (⟨g, hmem⟩ : FixedPoints.subring Γ(X,V) G)
      (FixedPoints.subring Γ(X, X.basicOpen h) G) :=
    Work.SymQuot.Invariants.fixedPoints_isLocalization_away hcompat g hmem
  have hOI : IsOpenImmersion (Work.SymQuot.GAction.chartRes A (X.basicOpen h) V hle hVi hW) := by
    show IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Work.SymQuot.GAction.invariantsRes A (X.basicOpen h) V hle hVi hW)))
    rw [show Work.SymQuot.GAction.invariantsRes A (X.basicOpen h) V hle hVi hW
        = algebraMap (FixedPoints.subring Γ(X,V) G) (FixedPoints.subring Γ(X, X.basicOpen h) G)
        from RingHom.ext fun s => Subtype.ext (by
          show (Work.SymQuot.GAction.invariantsRes A (X.basicOpen h) V hle hVi hW s :
              Γ(X, X.basicOpen h))
            = (algebraMap (FixedPoints.subring Γ(X,V) G)
                (FixedPoints.subring Γ(X, X.basicOpen h) G) s : Γ(X, X.basicOpen h))
          rw [Work.SymQuot.GAction.invariantsRes_apply, RingHom.algebraMap_toAlgebra]
          show Work.SymQuot.GAction.restrictSections (X.basicOpen h) V hle (s : Γ(X,V))
            = (Work.SymQuot.fixedPointsMap hcompat s : Γ(X, X.basicOpen h))
          rw [Work.SymQuot.fixedPointsMap_coe]
          show (X.presheaf.map (homOfLE hle).op).hom (s : Γ(X,V)) = _
          rw [← halg]
          rfl)]
    exact IsOpenImmersion.of_isLocalization (⟨g, hmem⟩ : FixedPoints.subring Γ(X,V) G)
  exact hOI

/-- The restriction map of charts `chart (X.basicOpen h) ⟶ chart V` is an isomorphism on stalks,
where `h` is a section over `U` fixed by the action whose basic open lies in `V`. -/
lemma stalkMap_chartRes_le (A : Work.SymQuot.GAction G X) {V U : X.Opens}
    (hVU : V ≤ U) (hV : IsAffineOpen V) (hVi : A.IsInvariantOpen V) (hUi : A.IsInvariantOpen U)
    (h : Γ(X,U)) (hh : ∀ g : G, Work.SymQuot.GAction.sectionHom A U hUi g h = h)
    (hle : X.basicOpen h ≤ V) (hW : A.IsInvariantOpen (X.basicOpen h))
    (z : Work.SymQuot.GAction.chart A (X.basicOpen h) hW) :
    IsIso ((Work.SymQuot.GAction.chartRes A (X.basicOpen h) V hle hVi hW).stalkMap z) :=
  (IsOpenImmersion.iff_isIso_stalkMap.mp
    (chartRes_isOpenImmersion_basicOpen_le A hVU hV hVi hUi h hh hle hW)).2 z

end Work.SymQuot.Chart

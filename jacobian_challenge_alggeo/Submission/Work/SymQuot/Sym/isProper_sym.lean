/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Symⁿ C` is proper over `K` (area SY)

The `n`-th symmetric power `Symⁿ C = Cⁿ/S_n` of a smooth proper curve is proper over `K`.

## Strategy

Write `X := Cⁿ = (prod C.toOver n).left`, `q := (Sym.quot C n).left : X ⟶ Q`,
`Q := (Sym C n).left`, `f := (prod C.toOver n).hom : X ⟶ Spec K` and `g := (Sym C n).hom`.

`IsProper g` is the conjunction of `IsSeparated g`, `UniversallyClosed g` and
`LocallyOfFiniteType g`, and we prove the three separately.

* **Universally closed** (`universallyClosed_sym` below): `q` is integral (hence universally
  closed, `Chart.quotientMap_isIntegralHom`) and surjective, and `q ≫ g = f` is proper (because
  `C` is proper, so `X = Cⁿ` is proper, `Prod.isProper_prod`).  Hence `g` is universally closed
  by `UniversallyClosed.of_comp_surjective`.

* **Separated** (`SymQuot/Sym/isSeparated_sym.lean`): `Δ := pullback.diagonal g` is an immersion,
  and `range Δ` is closed because `range Δ = (q × q) '' range (pullback.diagonal f)` (`q`
  surjective), `range (pullback.diagonal f)` is closed (`X` is proper over `K`) and `q × q` is
  closed (a composite of base changes of the universally closed `q`).

* **Locally of finite type** (`locallyOfFiniteType_sym_aux` below): `LocallyOfFiniteType` is
  Zariski-local at the source, and `Q` is covered by the charts `chartι U`.  On the chart of an
  invariant affine open `U ⊆ X`, the structure morphism `gU : Spec Γ(X,U)^{S_n} ⟶ Spec K` is the
  unique factorisation of `hU : Spec Γ(X,U) ⟶ Spec K` through `Spec.map (subtype)`
  (`Chart.existsUnique_affine_target`).  Its ring map `Spec.preimage gU` has underlying ring map
  the corestriction `κ` of `Spec.preimage hU` to the fixed points, so it suffices to know that
  `κ` is of finite type: this is Artin--Tate for the integral extension
  `Γ(X,U)^{S_n} ⊆ Γ(X,U)` (`Invariants.fixedPoints_isIntegral`) of finitely generated
  `K`-algebras (`SymQuot/Invariants/finiteType_fixedPoints`).
-/
import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Prod.isProper_prod
import Submission.Work.SymQuot.Invariants.fixedPoints_isIntegral
import Submission.Work.SymQuot.Sym.isSeparated_sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Sym

/-- **`Symⁿ C` is universally closed over `K`.**  The quotient map `Cⁿ ⟶ Symⁿ C` is integral
(hence universally closed) and surjective, and the structure morphism of the proper `K`-scheme
`Cⁿ` is its composite with the structure morphism of `Symⁿ C`. -/
theorem universallyClosed_sym {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) :
    UniversallyClosed (Work.SymQuot.Sym C n).hom := by
  haveI : Surjective (Work.SymQuot.Sym.quot C n).left :=
    ⟨Work.SymQuot.Sym.quot_surjective C n⟩
  haveI : UniversallyClosed
      ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom) :=
    (Work.SymQuot.Sym.quot_hom C n) ▸
      (Work.SymQuot.Prod.isProper_prod C.toOver n).toUniversallyClosed
  exact UniversallyClosed.of_comp_surjective (Work.SymQuot.Sym.quot C n).left
    (Work.SymQuot.Sym C n).hom

section LocallyOfFiniteType

/-- Restriction of sections along `V ≤ f ⁻¹ᵁ U`, composed with the open immersion `U.ι`: the
composite `resLE ≫ U.ι ≫ g` is `V.ι ≫ f ≫ g`. -/
private lemma resLE_comp_ι_assoc {X Y Z : Scheme} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (g : Y ⟶ Z) :
    Scheme.Hom.resLE f U V e ≫ U.ι ≫ g = V.ι ≫ f ≫ g := by
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- **Artin--Tate, fixed-point form.**  If `R` is a finite type `K`-algebra and
`κ : K →+* R^G` is a lift of the structure map `K → R` through the fixed points of a finite
group `G` acting on `R`, then `κ` is of finite type.  This is the Artin--Tate lemma
(`fg_of_fg_of_fg`) applied to the tower `K ⊆ R^G ⊆ R`: `R` is integral over `R^G`
(`fixedPoints_isIntegral`) and `R^G ⊆ R` is injective. -/
private theorem ringHom_finiteType_codRestrict_fixedPoints
    {K R : Type u} [CommRing K] [IsNoetherianRing K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] {G : Type u} [Group G] [Finite G] [MulSemiringAction G R]
    (κ : K →+* ↥(FixedPoints.subring R G))
    (hκ : ∀ k : K, (κ k : R) = algebraMap K R k) :
    RingHom.FiniteType κ := by
  letI : Algebra K ↥(FixedPoints.subring R G) := κ.toAlgebra
  have hst : IsScalarTower K ↥(FixedPoints.subring R G) R :=
    .of_algebraMap_eq fun k => (hκ k).symm
  haveI := hst
  haveI : Algebra.IsIntegral ↥(FixedPoints.subring R G) R :=
    Algebra.IsInvariant.isIntegral (A := ↥(FixedPoints.subring R G)) (B := R) (G := G)
  haveI : Algebra.FiniteType ↥(FixedPoints.subring R G) R :=
    Algebra.FiniteType.of_restrictScalars_finiteType K ↥(FixedPoints.subring R G) R
  haveI : Module.Finite ↥(FixedPoints.subring R G) R := Algebra.IsIntegral.finite
  have h := fg_of_fg_of_fg K ↥(FixedPoints.subring R G) R (Algebra.FiniteType.out)
    (Module.Finite.iff_fg.mp inferInstance) (fun _ _ hh => Subtype.ext hh)
  have h2 : Algebra.FiniteType K ↥(FixedPoints.subring R G) :=
    (Subalgebra.fg_iff_finiteType (⊤ : Subalgebra K ↥(FixedPoints.subring R G))).mp h
      |>.equiv Subalgebra.topEquiv
  exact h2

/-- **The structure morphism of a finite-group quotient is locally of finite type.**  Let `X` be
a scheme with an action of a finite group `Γ`, let `D` be a `QuotientData` for it (so that the
quotient `D.Quotient = X/Γ` exists) and let `f : X ⟶ Spec K` be a `Γ`-invariant morphism of
finite type.  Then the induced morphism `D.Quotient ⟶ Spec K` is locally of finite type.

`LocallyOfFiniteType` is local at the source, and the quotient is covered by the charts
`D.chartι U : Spec Γ(X,U)^Γ ⟶ D.Quotient`.  On the chart of `U`, the structure morphism is the
unique `gU` with `Spec.map (subtype) ≫ gU = hU` (`existsUnique_affine_target`), where
`hU = U.isoSpec.inv ≫ U.ι ≫ f`.  The ring map of `gU` is the corestriction of `Spec.preimage hU`
to the fixed points `Γ(X,U)^Γ`, which is of finite type by Artin--Tate
(`ringHom_finiteType_codRestrict_fixedPoints`). -/
private theorem locallyOfFiniteType_quotientHom
    {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}}
    (D : QuotientData Γ X) {K : Type u} [CommRing K] [IsNoetherianRing K]
    (f : X ⟶ Spec (CommRingCat.of K))
    (hf : ∀ g : Γ, D.action.hom g ≫ f = f)
    [LocallyOfFiniteType f] :
    LocallyOfFiniteType (D.quotientHom f hf) := by
  classical
  haveI hloc : IsZariskiLocalAtSource (@LocallyOfFiniteType) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  let Ucov : (D.Quotient).OpenCover :=
    { I₀ := D.Chart
      X := fun U => D.chart U
      f := fun U => D.chartι U
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x => by
          obtain ⟨U, y, hy⟩ := D.chartι_jointly_surjective x
          exact ⟨U, y, hy⟩, fun U => inferInstance⟩ }
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) Ucov).mpr
    (fun U => ?_)
  show LocallyOfFiniteType (D.chartι U ≫ D.quotientHom f hf)
  letI : MulSemiringAction Γ ↥(Γ(X, U.1)) := D.action.sectionMulSemiringAction U.1 U.2.2
  set hU : Spec (CommRingCat.of ↥(Γ(X, U.1))) ⟶ Spec (CommRingCat.of K) :=
    U.2.1.isoSpec.inv ≫ (U.1.ι ≫ f) with hU_def
  have hU_lof : LocallyOfFiniteType hU := by
    rw [hU_def]
    infer_instance
  have hinv : ∀ g : Γ,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ ↥(Γ(X, U.1)) g)) ≫ hU = hU := by
    intro g
    rw [hU_def, Work.SymQuot.Chart.toRingHom_eq_sectionHom D.action U.2.2 g,
      Work.SymQuot.Chart.spec_map_sectionHom D.action U.2.1 U.2.2 g]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, resLE_comp_ι_assoc, hf g⁻¹]
  obtain ⟨gU, hgU, huniq⟩ :=
    Work.SymQuot.Chart.existsUnique_affine_target (G := Γ) hU hinv
  have hgU_lof : LocallyOfFiniteType gU := by
    set κ : K →+* ↥(Γ(X, U.1)) := (Spec.preimage hU).hom with hκ
    have hspecκ : Spec.map (CommRingCat.ofHom κ) = hU := by
      rw [hκ, CommRingCat.ofHom_hom]
      exact Spec.map_preimage hU
    have hφsub : (Spec.preimage gU) ≫ CommRingCat.ofHom
        (Subring.subtype (FixedPoints.subring ↥(Γ(X, U.1)) Γ)) = Spec.preimage hU := by
      have hpre := congrArg Spec.preimage hgU
      rw [Spec.preimage_comp, Spec.preimage_map] at hpre
      exact hpre
    letI : Algebra K ↥(Γ(X, U.1)) := κ.toAlgebra
    have hFT : RingHom.FiniteType κ := by
      have h1 : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom κ)) := by
        rw [hspecκ]; exact hU_lof
      exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
        (φ := CommRingCat.ofHom κ)).mp h1
    have hAFT : Algebra.FiniteType K ↥(Γ(X, U.1)) := by
      show RingHom.FiniteType (algebraMap K ↥(Γ(X, U.1)))
      rw [RingHom.algebraMap_toAlgebra]
      exact hFT
    haveI := hAFT
    have hy : ∀ k : K, (((Spec.preimage gU).hom k : ↥(FixedPoints.subring ↥(Γ(X, U.1)) Γ)) :
        ↥(Γ(X, U.1))) = algebraMap K ↥(Γ(X, U.1)) k := by
      intro k
      rw [RingHom.algebraMap_toAlgebra]
      rw [hκ]
      have h1 : ((Spec.preimage gU ≫ CommRingCat.ofHom
          (Subring.subtype (FixedPoints.subring ↥(Γ(X, U.1)) Γ))).hom) k
          = (Spec.preimage hU).hom k := by
        rw [hφsub]
      exact h1
    have hψ : RingHom.FiniteType (Spec.preimage gU).hom :=
      ringHom_finiteType_codRestrict_fixedPoints (G := Γ) (Spec.preimage gU).hom hy
    rw [← Spec.map_preimage gU]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := Spec.preimage gU)).mpr hψ
  have hXX : Spec.map (CommRingCat.ofHom
      (FixedPoints.subring ↥(Γ(X, U.1)) Γ).subtype) ≫
      (D.chartι U ≫ D.quotientHom f hf) = hU := by
    have h1 : (U.2.1.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (FixedPoints.subring ↥(Γ(X, U.1)) Γ).subtype)) ≫
        (D.chartι U ≫ D.quotientHom f hf) = U.1.ι ≫ f := by
      rw [IsAffineOpen.isoSpec_hom U.2.1, ← GAction.chartMap, ← Category.assoc,
        ← D.quotientMap_chartι U, Category.assoc, D.quotientMap_quotientHom f hf]
    rw [hU_def, ← h1]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
  rw [huniq _ hXX]
  exact hgU_lof

/-- **`Symⁿ C` is locally of finite type over `K`.**

(Note: the file `SymQuot/Sym/locallyOfFiniteType_sym.lean` contains an independent attempt at
this statement under the name `locallyOfFiniteType_sym`; the proof below is self-contained and
does not depend on that file.) -/
theorem locallyOfFiniteType_sym_aux {K : Type u} [Field K]
    (C : Work.CurveBasics.Curve K) (n : ℕ) :
    LocallyOfFiniteType (Work.SymQuot.Sym C n).hom := by
  haveI : Work.SymQuot.CurveAffineCover C := inferInstance
  haveI : IsProper (Work.SymQuot.prod C.toOver n).hom :=
    Work.SymQuot.Prod.isProper_prod C.toOver n
  rw [Work.SymQuot.Sym.hom_def]
  exact locallyOfFiniteType_quotientHom (Work.SymQuot.symData C n)
    (Over.hom (Work.SymQuot.prod C.toOver n)) (Work.SymQuot.sym_hom_invariant C n)

end LocallyOfFiniteType

theorem isProper_sym {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) : AlgebraicGeometry.IsProper (Work.SymQuot.Sym C n).hom := by
  haveI : IsSeparated (Work.SymQuot.Sym C n).hom := isSeparated_sym C n
  haveI : UniversallyClosed (Work.SymQuot.Sym C n).hom := universallyClosed_sym C n
  haveI : LocallyOfFiniteType (Work.SymQuot.Sym C n).hom := locallyOfFiniteType_sym_aux C n
  exact IsProper.mk

end Work.SymQuot.Sym

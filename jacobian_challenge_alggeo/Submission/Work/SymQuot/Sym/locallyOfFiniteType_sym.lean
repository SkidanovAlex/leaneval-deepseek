import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Prod.isProper_prod
import Submission.Work.SymQuot.Invariants.fixedPoints_isIntegral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Sym

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
theorem ringHom_finiteType_codRestrict_fixedPoints
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
`hU = U.toSpecΓ⁻¹ ≫ U.ι ≫ f`.  The ring map of `gU` is the corestriction of the structure map
`κ` of `Γ(X,U)` to the fixed points `Γ(X,U)^Γ`; since `κ` is of finite type (as `hU` is locally of
finite type), this corestriction is of finite type by Artin--Tate
(`ringHom_finiteType_codRestrict_fixedPoints`). -/
theorem locallyOfFiniteType_quotientHom
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
    have hspec : Spec.map (CommRingCat.ofHom (Spec.preimage hU).hom) = hU := by
      show Spec.map (Spec.preimage hU) = hU
      exact Spec.map_preimage hU
    have hφsub : (FixedPoints.subring ↥(Γ(X, U.1)) Γ).subtype.comp
        (Spec.preimage gU).hom = (Spec.preimage hU).hom := by
      have hpre := congrArg Spec.preimage hgU
      rw [Spec.preimage_comp, Spec.preimage_map] at hpre
      exact congrArg CommRingCat.Hom.hom hpre
    letI : Algebra K ↥(Γ(X, U.1)) := (Spec.preimage hU).hom.toAlgebra
    haveI hFT : Algebra.FiniteType K ↥(Γ(X, U.1)) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
        (φ := Spec.preimage hU)).mp (by rw [Spec.map_preimage]; exact hU_lof)
    have hψ : RingHom.FiniteType (Spec.preimage gU).hom :=
      ringHom_finiteType_codRestrict_fixedPoints (G := Γ) (Spec.preimage gU).hom
        (fun k => RingHom.congr_fun hφsub k)
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

theorem locallyOfFiniteType_sym {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) :
    AlgebraicGeometry.LocallyOfFiniteType (Work.SymQuot.Sym C n).hom := by
  haveI : Work.SymQuot.CurveAffineCover C := inferInstance
  haveI : IsProper (prod C.toOver n).hom := Work.SymQuot.Prod.isProper_prod C.toOver n
  rw [Sym.hom_def]
  exact locallyOfFiniteType_quotientHom (symData C n) (Over.hom (prod C.toOver n))
    (sym_hom_invariant C n)

end Work.SymQuot.Sym

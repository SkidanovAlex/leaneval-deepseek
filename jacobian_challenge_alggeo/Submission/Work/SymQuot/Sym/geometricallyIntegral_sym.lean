import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Sym.geometricallyIrreducible_sym
import Submission.Work.SymQuot.Sym.isIntegral_sym
import Submission.Work.AbVar.SmoothReduced.geometricallyIntegral_of_smooth_of_geometricallyIrreducible
import Submission.Work.CurveBasics.All
import Submission.Work.SymQuot.RelQuot.relativeQuotAffinePieceAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical TensorProduct

universe u

namespace Work.SymQuot.Sym

variable {K : Type u} [Field K]

/-- **The chart of an invariant affine open is the quotient restricted to it.**  The composite
`Spec Γ(X,U)^Γ ⟶ U ⟶ X` of the `Spec` of the inclusion of the invariants with the chart
inclusion is `Spec Γ(X,U) ⟶ U ⟶ X/Γ`, one leg of the defining square of the quotient map. -/
theorem chartKey {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}}
    (D : Work.SymQuot.QuotientData Γ X) (U : D.Chart) :
    U.2.1.fromSpec ≫ D.quotientMap
      = Spec.map (CommRingCat.ofHom (Subring.subtype (D.action.invariants U.1 U.2.2)))
        ≫ D.chartι U := by
  rw [IsAffineOpen.fromSpec]
  rw [Category.assoc, Work.SymQuot.QuotientData.quotientMap_chartι]
  rw [Work.SymQuot.GAction.chartMap]
  simp only [Category.assoc, IsAffineOpen.isoSpec_inv_toSpecΓ_assoc]

/-- The action of a group of automorphisms of a `K`-scheme on the sections over an invariant
open fixes the constants (the sections pulled back from `Spec K`). -/
theorem smul_algebraMap_sections_eq {G : Type u} [Group G] {X : Scheme.{u}}
    (A : Work.SymQuot.GAction G X) (f : X ⟶ Spec (CommRingCat.of K))
    (hbase : ∀ g, A.hom g ≫ f = f)
    (U : X.Opens) (hU : A.IsInvariantOpen U) (h : G) (k : K) :
    letI : Algebra K Γ(X, U) :=
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra
    letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hU
    h • (algebraMap K Γ(X, U) k) = algebraMap K Γ(X, U) k := by
  letI : Algebra K Γ(X, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hU
  have hsmul : h • (algebraMap K Γ(X, U) k) =
      (A.hom h⁻¹).appLE U U (le_of_eq (hU h⁻¹).symm) (algebraMap K Γ(X, U) k) := rfl
  rw [hsmul]
  have key : f.appLE ⊤ U le_top ≫ (A.hom h⁻¹).appLE U U (le_of_eq (hU h⁻¹).symm)
      = f.appLE ⊤ U le_top :=
    (Scheme.Hom.appLE_comp_appLE (A.hom h⁻¹) f ⊤ U U (by exact le_top)
      (le_of_eq (hU h⁻¹).symm)).trans (Work.SymQuot.appLE_congr_hom (hbase h⁻¹) _ _)
  exact congrArg (fun (φ : Γ(Spec (CommRingCat.of K), ⊤) ⟶ Γ(X, U)) =>
    φ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k)) key

/-- The `MulSemiringAction` of the symmetric group on the sections `Γ(Cⁿ, U)` over a chart. -/
noncomputable instance instMulSemiringActionSections (C : Work.CurveBasics.Curve K) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] (U : (Work.SymQuot.symData C n).Chart) :
    MulSemiringAction (ULift.{u} (Equiv.Perm (Fin n)))
      Γ((Work.SymQuot.prod C.toOver n).left, U.1) :=
  (Work.SymQuot.symData C n).action.sectionMulSemiringAction U.1 U.2.2

/-- The action of `S_n` on the sections over a chart is by `K`-algebra automorphisms. -/
noncomputable instance instSMulCommClassSections (C : Work.CurveBasics.Curve K) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] (U : (Work.SymQuot.symData C n).Chart) :
    SMulCommClass (ULift.{u} (Equiv.Perm (Fin n))) K
      Γ((Work.SymQuot.prod C.toOver n).left, U.1) := by
  refine ⟨fun g k s => ?_⟩
  have hconst := smul_algebraMap_sections_eq (A := (Work.SymQuot.symData C n).action)
    (Work.SymQuot.prod C.toOver n).hom (Work.SymQuot.sym_hom_invariant C n) U.1 U.2.2 g k
  rw [Algebra.smul_def k s, MulSemiringAction.smul_mul, hconst, Algebra.smul_def k (g • s)]

/-- The `K`-algebra structure on the chart ring `A_U = Γ(Cⁿ,U)^{S_n}`. -/
noncomputable instance instAlgebraChartRing (C : Work.CurveBasics.Curve K) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] (U : (Work.SymQuot.symData C n).Chart) :
    Algebra K ↥(Work.SymQuot.GAction.chartRing (Work.SymQuot.symData C n).action U.1 U.2.2) :=
  inferInstanceAs (Algebra K ↥(FixedPoints.subalgebra K
    Γ((Work.SymQuot.prod C.toOver n).left, U.1) (ULift.{u} (Equiv.Perm (Fin n)))))

/-- **The sections of `Cⁿ` over an affine open, tensored with a field extension, form a
domain.**  `Cⁿ` is smooth over `K`, hence geometrically reduced, and geometrically irreducible,
so an affine open of `Cⁿ` is geometrically integral. -/
theorem isDomain_sections_tensor (C : Work.CurveBasics.Curve K) (n : ℕ)
    (U : (Work.SymQuot.prod C.toOver n).left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (L : Type u) [Field L] [Algebra K L] :
    IsDomain (TensorProduct K Γ((Work.SymQuot.prod C.toOver n).left, U) L) := by
  haveI hSm : Smooth ((Work.SymQuot.prod C.toOver n).hom) := Work.SymQuot.smooth_pi_prod C n
  haveI hGi : GeometricallyIrreducible ((Work.SymQuot.prod C.toOver n).hom) :=
    Work.SymQuot.Sym.geometricallyIrreducible_prod C.toOver n
  haveI hGI : GeometricallyIntegral ((Work.SymQuot.prod C.toOver n).hom) :=
    Work.AbVar.SmoothReduced.geometricallyIntegral_of_smooth_of_geometricallyIrreducible _
  haveI hInt : IsIntegral ((Work.SymQuot.prod C.toOver n).left) := Work.SymQuot.isIntegral_prod C n
  exact Work.CurveBasics.isDomain_tensor_of_isOpenImmersion (f := (Work.SymQuot.prod C.toOver n).hom)
    (A := Γ((Work.SymQuot.prod C.toOver n).left, U)) (i := hU.fromSpec)
    (Work.SymQuot.RelQuot.specMap_algebraMap_sections _ U hU).symm L

/-- **The `K`-structure of the sections over a chart is the restriction of the `K`-structure of
the sections of `Cⁿ`.**  The `K`-algebra structure of the chart ring is read off from its
structure morphism; this identifies it with the canonical one. -/
theorem subtype_comp_preimage_chartι (C : Work.CurveBasics.Curve K) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] (U : (Work.SymQuot.symData C n).Chart) :
    (Subring.subtype ((Work.SymQuot.symData C n).action.invariants U.1 U.2.2)).comp
      ((Spec.preimage ((Work.SymQuot.symData C n).chartι U ≫ (Work.SymQuot.Sym C n).hom)).hom)
    = algebraMap K Γ((Work.SymQuot.prod C.toOver n).left, U.1) := by
  have hQuot : (Work.SymQuot.symData C n).quotientMap ≫ (Work.SymQuot.Sym C n).hom
      = (Work.SymQuot.prod C.toOver n).hom := by
    rw [← Work.SymQuot.Sym.quot_left C n]
    exact Work.SymQuot.Sym.quot_hom C n
  have hS : Spec.map (CommRingCat.ofHom (Subring.subtype
        ((Work.SymQuot.symData C n).action.invariants U.1 U.2.2)))
      ≫ ((Work.SymQuot.symData C n).chartι U ≫ (Work.SymQuot.Sym C n).hom)
      = Spec.map (CommRingCat.ofHom (algebraMap K Γ((Work.SymQuot.prod C.toOver n).left, U.1))) := by
    have h1 : Spec.map (CommRingCat.ofHom (Subring.subtype
          ((Work.SymQuot.symData C n).action.invariants U.1 U.2.2)))
        ≫ (Work.SymQuot.symData C n).chartι U
        = U.2.1.fromSpec ≫ (Work.SymQuot.symData C n).quotientMap :=
      (chartKey (D := Work.SymQuot.symData C n) U).symm
    rw [← Category.assoc, h1, Category.assoc, hQuot]
    rw [Work.SymQuot.RelQuot.specMap_algebraMap_sections]
  have h2 : CommRingCat.ofHom ((Subring.subtype
        ((Work.SymQuot.symData C n).action.invariants U.1 U.2.2)).comp
      ((Spec.preimage ((Work.SymQuot.symData C n).chartι U ≫ (Work.SymQuot.Sym C n).hom)).hom))
      = CommRingCat.ofHom (algebraMap K Γ((Work.SymQuot.prod C.toOver n).left, U.1)) := by
    apply Spec.map_inj.mp
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [show CommRingCat.ofHom ((Spec.preimage
          ((Work.SymQuot.symData C n).chartι U ≫ (Work.SymQuot.Sym C n).hom)).hom)
        = (Spec.preimage ((Work.SymQuot.symData C n).chartι U
          ≫ (Work.SymQuot.Sym C n).hom)) from rfl]
    rw [Spec.map_preimage]
    exact hS
  exact congrArg CommRingCat.Hom.hom h2

/-- **The chart rings are geometrically reduced.**  The chart ring `A_U = Γ(Cⁿ,U)^{S_n}` is the
ring of invariants of the `S_n`-action on the geometrically integral ring `Γ(Cⁿ,U)`, so
`A_U ⊗[K] L` embeds into the reduced ring `Γ(Cⁿ,U) ⊗[K] L`. -/
theorem isReduced_chartRing_tensor (C : Work.CurveBasics.Curve K) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] (U : (Work.SymQuot.symData C n).Chart) [Nonempty U.1]
    (L : Type u) [Field L] [Algebra K L] :
    IsReduced (TensorProduct K ↥(Work.SymQuot.GAction.chartRing
      (Work.SymQuot.symData C n).action U.1 U.2.2) L) := by
  haveI hD : IsDomain (TensorProduct K Γ((Work.SymQuot.prod C.toOver n).left, U.1) L) :=
    isDomain_sections_tensor C n U.1 U.2.1 L
  haveI hB : IsReduced (TensorProduct K Γ((Work.SymQuot.prod C.toOver n).left, U.1) L) :=
    inferInstance
  have hinj : Function.Injective (Algebra.TensorProduct.map (FixedPoints.subalgebra K
      Γ((Work.SymQuot.prod C.toOver n).left, U.1) (ULift.{u} (Equiv.Perm (Fin n)))).val
        (AlgHom.id K L)).toRingHom :=
    TensorProduct.map_injective_of_flat_flat (R := K)
      (f := (FixedPoints.subalgebra K Γ((Work.SymQuot.prod C.toOver n).left, U.1)
        (ULift.{u} (Equiv.Perm (Fin n)))).val.toLinearMap)
      (g := (LinearMap.id : L →ₗ[K] L)) (fun _ _ h => Subtype.ext h) (fun _ _ h => h)
  exact isReduced_of_injective _ hinj

/-- **The base change of a chart is reduced.**  The chart `Spec A_U` has structure morphism
`Spec.map (algebraMap K A_U)`, so its base change to `L` is `Spec (A_U ⊗[K] L)`. -/
theorem isReduced_chart_pullback (C : Work.CurveBasics.Curve K) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] (U : (Work.SymQuot.symData C n).Chart) [Nonempty U.1]
    (L : Type u) [Field L] [Algebra K L] :
    IsReduced (pullback ((Work.SymQuot.symData C n).chartι U ≫ (Work.SymQuot.Sym C n).hom)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
  have hred := isReduced_chartRing_tensor C n U L
  have hχ : (algebraMap K ↥(Work.SymQuot.GAction.chartRing
        (Work.SymQuot.symData C n).action U.1 U.2.2))
      = ((Spec.preimage ((Work.SymQuot.symData C n).chartι U
          ≫ (Work.SymQuot.Sym C n).hom)).hom) := by
    ext k
    change algebraMap K Γ((Work.SymQuot.prod C.toOver n).left, U.1) k
      = (Subring.subtype ((Work.SymQuot.symData C n).action.invariants U.1 U.2.2))
          ((Spec.preimage ((Work.SymQuot.symData C n).chartι U
            ≫ (Work.SymQuot.Sym C n).hom)).hom k)
    exact (congrArg (fun (f : K →+* Γ((Work.SymQuot.prod C.toOver n).left, U.1)) => f k)
      (subtype_comp_preimage_chartι C n U)).symm
  have hiso : pullback (Spec.map (CommRingCat.ofHom (algebraMap K ↥(Work.SymQuot.GAction.chartRing
        (Work.SymQuot.symData C n).action U.1 U.2.2))))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      ≅ pullback ((Work.SymQuot.symData C n).chartι U ≫ (Work.SymQuot.Sym C n).hom)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    pullback.congrHom (by
      rw [hχ, show CommRingCat.ofHom ((Spec.preimage ((Work.SymQuot.symData C n).chartι U
          ≫ (Work.SymQuot.Sym C n).hom)).hom)
        = (Spec.preimage ((Work.SymQuot.symData C n).chartι U
          ≫ (Work.SymQuot.Sym C n).hom)) from rfl, Spec.map_preimage]) rfl
  have hspec : IsReduced (Spec (CommRingCat.of (TensorProduct K
      ↥(Work.SymQuot.GAction.chartRing (Work.SymQuot.symData C n).action U.1 U.2.2) L))) :=
    (affine_isReduced_iff _).mpr hred
  exact ObjectProperty.prop_of_iso (fun X : Scheme.{u} => IsReduced X)
    ((AlgebraicGeometry.pullbackSpecIso K ↥(Work.SymQuot.GAction.chartRing
      (Work.SymQuot.symData C n).action U.1 U.2.2) L).symm ≪≫ hiso) hspec

/-- **The base change of `Symⁿ C` to a field extension is reduced.**  The quotient `Symⁿ C` is
covered by the charts `Spec Γ(Cⁿ,U)^{S_n}` over the nonempty invariant affine opens `U`; pulling
this cover back along the projection to `Symⁿ C` covers the base change, and each piece is the
base change of a chart, hence reduced by `isReduced_chart_pullback`. -/
theorem isReduced_pullback_sym (C : Work.CurveBasics.Curve K) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] (L : Type u) [Field L] [Algebra K L] :
    IsReduced (pullback (Work.SymQuot.Sym C n).hom
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
  let y := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let 𝒰 : (pullback (Work.SymQuot.Sym C n).hom y).OpenCover :=
    { I₀ := {U : (Work.SymQuot.symData C n).Chart // Nonempty U.1}
      X := fun i => pullback ((Work.SymQuot.symData C n).chartι i.1)
        (pullback.fst (Work.SymQuot.Sym C n).hom y)
      f := fun i => pullback.snd ((Work.SymQuot.symData C n).chartι i.1)
        (pullback.fst (Work.SymQuot.Sym C n).hom y)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun z => ?_, fun i => inferInstance⟩
        obtain ⟨U, p, hp⟩ := (Work.SymQuot.symData C n).chartι_jointly_surjective
          (pullback.fst (Work.SymQuot.Sym C n).hom y z)
        have hU : Nonempty U.1 := by
          obtain ⟨x, _⟩ := Work.SymQuot.Chart.chartMap_surjective (Work.SymQuot.symData C n).action
            U.2.1 U.2.2 p
          exact ⟨x.1, x.2⟩
        refine ⟨⟨U, hU⟩, ?_⟩
        obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := (Work.SymQuot.symData C n).chartι U)
          (g := pullback.fst (Work.SymQuot.Sym C n).hom y) p z hp
        exact ⟨w, hw⟩ }
  haveI : ∀ i, IsReduced (𝒰.X i) := fun i => by
    haveI : Nonempty i.1.1 := i.2
    exact ObjectProperty.prop_of_iso (fun X : Scheme.{u} => IsReduced X)
      (pullbackRightPullbackFstIso (Work.SymQuot.Sym C n).hom y
        ((Work.SymQuot.symData C n).chartι i.1)).symm
      (isReduced_chart_pullback C n i.1 L)
  exact IsReduced.of_openCover _ 𝒰

/-- `Symⁿ C` is geometrically reduced over `K`. -/
theorem geometricallyReduced_sym (C : Work.CurveBasics.Curve K) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] :
    GeometricallyReduced (Work.SymQuot.Sym C n).hom := by
  rw [GeometricallyReduced.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
      (P := fun X : Scheme.{u} => IsReduced X)]
  intro L _ _
  exact isReduced_pullback_sym C n L

open CategoryTheory Limits AlgebraicGeometry in
theorem geometricallyIntegral_sym {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    [Work.SymQuot.CurveAffineCover C] :
    GeometricallyIntegral (Work.SymQuot.Sym C n).hom := by
  haveI hred : GeometricallyReduced (Work.SymQuot.Sym C n).hom := geometricallyReduced_sym C n
  haveI hirr : GeometricallyIrreducible (Work.SymQuot.Sym C n).hom :=
    Work.SymQuot.Sym.geometricallyIrreducible_sym C n
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

end Work.SymQuot.Sym

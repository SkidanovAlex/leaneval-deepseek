import Mathlib
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.NK.CFTLib.HR.TransferAux.towerAux
import Submission.NK.CFTLib.HR.TransferAux.invariantsAux
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1

/-!
# Injectivity of the local level map

The "local Hilbert 90 / norm tower" step of the Brauer transfer: for a tower `K ⊆ M ⊆ E` of finite
Galois extensions of number fields and places `W | w`, the local level map

`localLevelMap : H²(Γ_w, M_wˣ) ⟶ H²(Γ_W, E_Wˣ)`

(restriction of decomposition groups together with the local coefficient map `M_wˣ → E_Wˣ`,
`NK.NUV2.LC.RouteB.localLevelMap`) is injective.

The proof identifies `localLevelMap` with the edge map of the inflation–restriction sequence for the
normal subgroup `S = ker (Γ_W → Γ_w)` (the relative decomposition group `Gal(E_W/M_w)`) conjugated by
the Galois-descent identification `(E_Wˣ)^S ≅ M_wˣ` of the coefficient modules
(`Submission/Work/CFTLib/HR/TransferAux/invariantsAux.lean`); the edge map is injective because
`H¹(S, E_Wˣ) = 0` (Hilbert 90, `TowerAux.subsingleton_h1_ker_localStabilizerMapTower`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace NK.CFTLib.HR.TransferAux

/-- **Injectivity of the local level map** (the "local Hilbert 90 / norm tower" step of the Brauer
transfer).

For a tower `K ⊆ M ⊆ E` of finite Galois extensions of number fields, a place `w` of `M` and a place
`W` of `E` above `w`, the local level map

`localLevelMap : H²(Γ_w, M_wˣ) → H²(Γ_W, E_Wˣ)`

(restriction of decomposition groups `Γ_W → Γ_w` together with the local coefficient map
`M_wˣ → E_Wˣ`, `NK.NUV2.LC.RouteB.localLevelMap`) is injective.

Mathematically it is the inclusion of Brauer groups `Br(M_w/K_v) ⊆ Br(E_W/K_v)`; its dual shadow is
the norm tower inclusion `N_{E_W/K_v}(E_Wˣ) ⊆ N_{M_w/K_v}(M_wˣ)`.  A route: identify
`localLevelMap` as `map(stabRestrict, localCoeff)`, factor the pullback of cocycles through the
quotient by `S = Γ_W ∩ Gal(E/M)` (whose quotient is the decomposition group `Γ_w` of `M`, using
`stabRestrict` plus transitivity of the Galois action on the places above `w`,
`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`), and use the exactness/injectivity
of the inflation map for the normal subgroup `S ≤ Γ_W` with `H¹(S, E_Wˣ) = 0` (Hilbert 90, e.g.
`NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep` for the local field extension
`E_W/M_w`, or `Commons.…subsingleton_groupCohomology_one_res_units`), together with the identification
`(E_Wˣ)^S = M_wˣ` of the invariants with the units of the fixed field (the generic
`NatCardP9.unitsInvLinearEquiv` machinery of
`Submission/Commons/NumberTheory/NumberField/Completion/natCard_quotient_units_range_norm_adicCompletion_of_commute.lean`
applies to any finite Galois extension of fields, in particular to `E_W/M_w`).  The maps
`stabRestrict`/`localCoeff` and the naturality square `locUnits_inflation_eq` are already proved in
`Submission/Work/NUV2/ARL/HR/locUnits_inflation_eq_zero_iff.lean` and
`Submission/Work/NUV2/LC/RouteB/locUnits_tower_eq_zero.lean`. -/
theorem localLevelMap_injective_vanishing {K M E : Type} [Field K] [NumberField K]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E]
    [IsScalarTower K M E] [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M]
    [IsGalois K E] [IsGalois M E]
    (w : NK.GlobalCFT.Place M) (W : NK.GlobalCFT.Place E)
    (h : NK.GlobalCFT.Place.LiesOver W w)
    (y : groupCohomology (NK.HassePrinciple.localUnitsRep K M w) 2)
    (hy : (NK.NUV2.LC.RouteB.localLevelMap (F := K) (L := M) (M := E) h).hom y = 0) : y = 0 := by
  classical
  -- ### Setup
  let f := NK.NUV2.LC.RouteB.localStabilizerMapTower (F := K) (L := M) (M := E) h
  have hf : Function.Surjective f := TowerAux.localStabilizerMapTower_surjective h
  let S : Subgroup ↥(MulAction.stabilizer Gal(E/K) W) := f.ker
  haveI hSn : S.Normal := inferInstance
  let e : ↥(MulAction.stabilizer Gal(M/K) w) ≃* (↥(MulAction.stabilizer Gal(E/K) W) ⧸ S) :=
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm
  have he_mk : ∀ γ : ↥(MulAction.stabilizer Gal(E/K) W),
      e.symm (QuotientGroup.mk' S γ) = f γ := fun γ => rfl
  have hf_eq : f = e.symm.toMonoidHom.comp (QuotientGroup.mk' S) :=
    MonoidHom.ext fun γ => (he_mk γ).symm
  let A : Rep.{0,0,0} NK.HassePrinciple.CoeffInt ↥(MulAction.stabilizer Gal(E/K) W) :=
    NK.HassePrinciple.localUnitsRep K E W
  let B : Rep.{0,0,0} NK.HassePrinciple.CoeffInt ↥(MulAction.stabilizer Gal(M/K) w) :=
    NK.HassePrinciple.localUnitsRep K M w
  let θ : Rep.res f B ⟶ A := NK.NUV2.LC.RouteB.localUnitsMapTowerCoeff (F := K) (L := M) (M := E) h
  letI : AddCommGroup B.V := B.hV1
  letI : Module NK.HassePrinciple.CoeffInt B.V := B.hV2
  letI : AddCommGroup (A.quotientToInvariants S).V := (A.quotientToInvariants S).hV1
  letI : Module NK.HassePrinciple.CoeffInt (A.quotientToInvariants S).V :=
    (A.quotientToInvariants S).hV2
  have hkey : ∀ z : B.V, θ.hom z
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits W w h (Additive.toMul z)) :=
    fun z => rfl
  have hθinj : Function.Injective θ.hom := by
    intro x x' hxx
    rw [hkey x, hkey x'] at hxx
    have h2 := Additive.ofMul.injective hxx
    have h3 := NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective h h2
    show x = x'
    rw [← ofMul_toMul x, ← ofMul_toMul x']
    exact congrArg Additive.ofMul h3
  -- ### The coefficient linear equivalence `(E_Wˣ)^S ≅ M_wˣ`
  let ι₀ : B.V →ₗ[NK.HassePrinciple.CoeffInt] (A.quotientToInvariants S).V :=
    { toFun := fun x => ⟨θ.hom x, fun σ => unitsMapTowerCoeff_mem_invariants h σ (Additive.toMul x)⟩
      map_add' := fun x x' => Subtype.ext (map_add θ.hom x x')
      map_smul' := fun c x => Subtype.ext (map_smul θ.hom c x) }
  have hι₀_bij : Function.Bijective ι₀ := by
    constructor
    · intro x x' hxx
      exact hθinj (congrArg Subtype.val hxx)
    · intro z
      obtain ⟨u, hu⟩ := unitsMapTowerCoeff_surj_invariants (F := K) (L := M) (M := E) h z.1 z.2
      exact ⟨Additive.ofMul u, Subtype.ext hu⟩
  let ι : B.V ≃ₗ[NK.HassePrinciple.CoeffInt] (A.quotientToInvariants S).V :=
    LinearEquiv.ofBijective ι₀ hι₀_bij
  have hι_apply : ∀ x : B.V, (ι x).1 = θ.hom x := fun x => rfl
  -- ### The equivariance of `ι`
  have hact : ∀ (γ : ↥(MulAction.stabilizer Gal(E/K) W)) (z : (A.quotientToInvariants S).V),
      ((A.quotientToInvariants S).ρ (QuotientGroup.mk' S γ) z).1 = A.ρ γ z.1 := fun γ z => rfl
  have hequiv : ∀ (γ : ↥(MulAction.stabilizer Gal(E/K) W)) (x : B.V),
      A.ρ γ (θ.hom x) = θ.hom (B.ρ (f γ) x) := by
    intro γ x
    have heq := congrArg (fun (u : B.V →ₗ[NK.HassePrinciple.CoeffInt] A.V) => u x)
      ((Rep.Hom.hom θ).isIntertwining' γ)
    exact heq.symm
  have he : ∀ g : ↥(MulAction.stabilizer Gal(M/K) w),
      ι.toLinearMap ∘ₗ B.ρ g = (A.quotientToInvariants S).ρ (e g) ∘ₗ ι.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨γ, hγ⟩ := QuotientGroup.mk'_surjective S (e g)
    have hfγ : f γ = g := by
      have h1 : e.symm (QuotientGroup.mk' S γ) = e.symm (e g) := by rw [hγ]
      rw [he_mk γ] at h1
      simpa using h1
    change (ι.toLinearMap ((B.ρ g) x) : (A.quotientToInvariants S).V)
      = ((A.quotientToInvariants S).ρ (e g)) (ι.toLinearMap x)
    apply Subtype.ext
    rw [show (ι.toLinearMap ((B.ρ g) x) : (A.quotientToInvariants S).V).1 = θ.hom (B.ρ g x)
        from rfl,
      ← hγ, hact γ (ι.toLinearMap x),
      show (ι.toLinearMap x : (A.quotientToInvariants S).V).1 = θ.hom x from rfl,
      hequiv γ x, hfγ]
  have heΦ : ∀ q : (↥(MulAction.stabilizer Gal(E/K) W) ⧸ S),
      ι.toLinearMap ∘ₗ (Rep.res e.symm.toMonoidHom B).ρ q
        = (A.quotientToInvariants S).ρ q ∘ₗ ι.toLinearMap := by
    intro q
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective S q
    apply LinearMap.ext
    intro x
    change (ι.toLinearMap (((Rep.res e.symm.toMonoidHom B).ρ (QuotientGroup.mk' S γ)) x) :
        (A.quotientToInvariants S).V)
      = ((A.quotientToInvariants S).ρ (QuotientGroup.mk' S γ)) (ι.toLinearMap x)
    apply Subtype.ext
    rw [show (ι.toLinearMap (((Rep.res e.symm.toMonoidHom B).ρ (QuotientGroup.mk' S γ)) x) :
          (A.quotientToInvariants S).V).1 = θ.hom (((Rep.res e.symm.toMonoidHom B).ρ
            (QuotientGroup.mk' S γ)) x) from rfl,
      show ((Rep.res e.symm.toMonoidHom B).ρ (QuotientGroup.mk' S γ)) x
        = (B.ρ (f γ)) x from rfl,
      show θ.hom ((B.ρ (f γ)) x) = θ.hom ((B.ρ (f γ)) x) from rfl,
      hact γ (ι.toLinearMap x),
      show (ι.toLinearMap x : (A.quotientToInvariants S).V).1 = θ.hom x from rfl,
      hequiv γ x]
  -- ### The Galois-descent isomorphism
  let Φ : Rep.res e.symm.toMonoidHom B ⟶ A.quotientToInvariants S :=
    Rep.ofHom ⟨ι.toLinearMap, heΦ⟩
  have hΦ_apply : ∀ x : B.V, (Rep.Hom.hom Φ).toLinearMap x = ι x := fun x => rfl
  have hmap_id_comp : groupCohomology.map f (𝟙 (Rep.res f B)) 2
      ≫ groupCohomology.map (MonoidHom.id ↥(MulAction.stabilizer Gal(E/K) W)) θ 2
      = groupCohomology.map f θ 2 := by
    rw [← groupCohomology.map_comp]
    refine groupCohomology.map_congr (MonoidHom.comp_id f) ?_ 2
    rw [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap, Rep.hom_id]
    rfl
  have hΘlin : (Rep.Hom.hom ((Rep.resFunctor (QuotientGroup.mk' S)).map Φ
      ≫ Rep.ofHom (A.ρ.quotientToInvariants_lift S))).toLinearMap = (Rep.Hom.hom θ).toLinearMap := by
    rw [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap, Rep.hom_ofHom]
    apply LinearMap.ext
    intro x
    show (A.ρ.quotientToInvariants_lift S).toLinearMap (ι x) = θ.hom x
    rw [show (A.ρ.quotientToInvariants_lift S).toLinearMap (ι x) = (ι x).1 from rfl, hι_apply]
  have hdescent : groupCohomology.map (e.symm.toMonoidHom) Φ 2
      = (groupCohomology.mapIso e ι he 2).hom := (groupCohomology.mapIso_hom e ι he 2).symm
  let infMap : groupCohomology (A.quotientToInvariants S) 2 ⟶ groupCohomology A 2 :=
    groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2
  have hcomp := groupCohomology.map_comp (f := e.symm.toMonoidHom) (g := QuotientGroup.mk' S)
    Φ (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2
  have hloc : (NK.NUV2.LC.RouteB.localLevelMap (F := K) (L := M) (M := E) h)
      = groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' S))
          ((Rep.resFunctor (QuotientGroup.mk' S)).map Φ
            ≫ Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 := by
    rw [show (NK.NUV2.LC.RouteB.localLevelMap (F := K) (L := M) (M := E) h)
        = groupCohomology.map f (𝟙 (Rep.res f B)) 2
          ≫ groupCohomology.map (MonoidHom.id ↥(MulAction.stabilizer Gal(E/K) W)) θ 2 from rfl,
      hmap_id_comp]
    exact (groupCohomology.map_congr hf_eq hΘlin 2).symm
  have hmain : (NK.NUV2.LC.RouteB.localLevelMap (F := K) (L := M) (M := E) h)
      = (groupCohomology.mapIso e ι he 2).symm.inv ≫ infMap := by
    calc (NK.NUV2.LC.RouteB.localLevelMap (F := K) (L := M) (M := E) h)
        = groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' S))
            ((Rep.resFunctor (QuotientGroup.mk' S)).map Φ
              ≫ Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 := hloc
      _ = groupCohomology.map e.symm.toMonoidHom Φ 2 ≫ infMap := hcomp
      _ = (groupCohomology.mapIso e ι he 2).hom ≫ infMap :=
          congrArg (fun z => z ≫ infMap) hdescent
      _ = (groupCohomology.mapIso e ι he 2).symm.inv ≫ infMap := by
          rw [Iso.symm_inv]
  -- ### Conclusion
  have hinfInj : Function.Injective ⇑infMap.hom :=
    Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1_general
      S A (TowerAux.subsingleton_h1_ker_localStabilizerMapTower h)
  rw [hmain] at hy
  rw [ModuleCat.comp_apply] at hy
  have h2 : (groupCohomology.mapIso e ι he 2).symm.inv y = 0 := hinfInj (by
    have h3 : infMap.hom ((groupCohomology.mapIso e ι he 2).symm.inv y) = infMap.hom 0 := by
      rw [hy, map_zero]
    exact h3)
  have h5 : (groupCohomology.mapIso e ι he 2).symm.hom
      ((groupCohomology.mapIso e ι he 2).symm.inv y) = 0 := by
    rw [h2, map_zero]
  have h6 := Iso.inv_hom_id (groupCohomology.mapIso e ι he 2).symm
  have h7 := congrArg (fun (f : groupCohomology B 2 ⟶ groupCohomology B 2) =>
    (ConcreteCategory.hom f) y) h6
  rw [ModuleCat.comp_apply, ModuleCat.id_apply] at h7
  rw [h7] at h5
  exact h5


end NK.CFTLib.HR.TransferAux

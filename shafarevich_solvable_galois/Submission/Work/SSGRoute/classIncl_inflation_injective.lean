import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.classIncl_isCanonical
import Submission.Work.SSGRoute.Phi0Aux
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
import Submission.NK.GlobalCFTdeep.H1All
import Submission.NK.HassePrinciple.subsingleton_classGroupRep_one
import Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Injectivity of the level inflation `H²(Gal(F/k), C_F) → H²(Gal(L/k), C_L)`

For a tower of number fields `k ⊆ F ⊆ L` with `F/k` and `L/k` finite Galois, the map
`H²(Gal(F/k), C_F) → H²(Gal(L/k), C_L)` induced by the restriction `Gal(L/k) → Gal(F/k)` and the
canonical inclusion of idèle class groups `C_F → C_L` is injective.

The proof factors this map through the standard inflation of the normal subgroup
`S = ker (galRes k F L) ≤ Gal(L/k)`:
`H²(Gal(F/k), C_F) → H²(Gal(L/k)/S, C_L^S) → H²(Gal(L/k), C_L)`,
the first map being an isomorphism (the canonical inclusion identifies `C_F` with `C_L^S`,
`classIncl_inj_surj_invariants`) and the second the inflation along `S`, injective because
`H¹(S, C_L) = 0` (`subsingleton_classesK_res_one`,
`Commons…H2_inflation_injective_of_subsingleton_H1_general`).
-/

namespace Work.SSGRoute

open CategoryTheory
open SSGRoute.PTExt
open NK.GlobalCFT

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem H2_map_injective_of_ker_coeff {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (A : Rep.{0,0,0} k H) (B : Rep.{0,0,0} k G) (φ : Rep.res f A ⟶ B)
    (hφinj : Function.Injective φ.hom)
    (hφsurj : ∀ b : B.V, (∀ s : f.ker, B.ρ s.1 b = b) → ∃ a : A.V, φ.hom a = b)
    (hB : Subsingleton (groupCohomology (Rep.res f.ker.subtype B) 1)) :
    Function.Injective (groupCohomology.map f φ 2).hom := by
  classical
  have hinv_apply : ∀ (s : f.ker) (x : A.V),
      B.ρ s.1 ((Rep.Hom.hom φ) x) = (Rep.Hom.hom φ) x := by
    intro s x
    have h1 : (Rep.Hom.hom φ) ((Rep.res f A).ρ s.1 x) = B.ρ s.1 ((Rep.Hom.hom φ) x) :=
      LinearMap.congr_fun ((Rep.Hom.hom φ).isIntertwining' s.1) x
    have h2 : (Rep.res f A).ρ s.1 x = x := by
      change A.ρ (f s.1) x = x
      rw [MonoidHom.mem_ker.mp s.2, map_one, Module.End.one_apply]
    rw [← h1, h2]
  let g : A.V →ₗ[k] ↥(Representation.invariants (B.ρ.comp f.ker.subtype)) :=
    LinearMap.codRestrict (Representation.invariants (B.ρ.comp f.ker.subtype)) (Rep.Hom.hom φ).toLinearMap
      (fun a => (Representation.mem_invariants (B.ρ.comp f.ker.subtype) _).mpr (fun s => hinv_apply s a))
  have g_apply : ∀ a : A.V, (g a : B.V) = (Rep.Hom.hom φ) a := fun a => rfl
  have hint : ∀ q : G ⧸ f.ker,
      g ∘ₗ (Rep.res (QuotientGroup.kerLift f) A).ρ q
        = (B.quotientToInvariants f.ker).ρ q ∘ₗ g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective f.ker q
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    show (Rep.Hom.hom φ) (A.ρ ((QuotientGroup.kerLift f) (QuotientGroup.mk' f.ker x)) a)
      = B.ρ x ((Rep.Hom.hom φ) a)
    have hkx : (QuotientGroup.kerLift f) (QuotientGroup.mk' f.ker x) = f x := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk]
    rw [hkx]
    exact LinearMap.congr_fun ((Rep.Hom.hom φ).isIntertwining' x) a
  let e : Rep.res (QuotientGroup.kerLift f) A ⟶ B.quotientToInvariants f.ker :=
    Rep.ofHom ⟨g, hint⟩
  have hg_inj : Function.Injective g := by
    intro a1 a2 h
    exact hφinj (by simpa [g_apply] using congrArg Subtype.val h)
  have hg_surj : Function.Surjective g := by
    intro b
    have hb : ∀ s : f.ker, B.ρ s.1 (b : B.V) = (b : B.V) :=
      fun s => (Representation.mem_invariants (B.ρ.comp f.ker.subtype) _).mp b.2 s
    obtain ⟨a, ha⟩ := hφsurj (b : B.V) hb
    exact ⟨a, Subtype.ext (by rw [g_apply]; exact ha)⟩
  haveI : IsIso e := (isIso_iff_mono_and_epi e).mpr
    ⟨(Rep.mono_iff_injective e).mpr (by simpa [e] using hg_inj),
     (Rep.epi_iff_surjective e).mpr (by simpa [e] using hg_surj)⟩
  have hcomp : (QuotientGroup.kerLift f).comp (QuotientGroup.mk' f.ker) = f := by
    ext x
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk]
  have hfac : (Rep.resFunctor (QuotientGroup.mk' f.ker)).map e
      ≫ Rep.ofHom (B.ρ.quotientToInvariants_lift f.ker) = φ := by
    apply Rep.hom_ext
    rw [Rep.hom_comp]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    rfl
  have hkey : groupCohomology.map f φ 2
      = groupCohomology.map (QuotientGroup.kerLift f) e 2
        ≫ (groupCohomology.infNatTrans k f.ker 2).app B := by
    have h1 : groupCohomology.map f φ 2
        = groupCohomology.map ((QuotientGroup.kerLift f).comp (QuotientGroup.mk' f.ker))
            ((Rep.resFunctor (QuotientGroup.mk' f.ker)).map e
              ≫ Rep.ofHom (B.ρ.quotientToInvariants_lift f.ker)) 2 :=
      groupCohomology.map_congr hcomp.symm
        (Eq.symm (congrArg (fun (ψ : Rep.res f A ⟶ B) => (Rep.Hom.hom ψ).toLinearMap) hfac)) 2
    rw [h1, groupCohomology.map_comp]
    congr 1
  have hsurj : Function.Surjective (QuotientGroup.kerLift f) := fun y => by
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk' f.ker x, by rw [QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk]⟩
  let eH : (G ⧸ f.ker) ≃* H := MulEquiv.ofBijective (QuotientGroup.kerLift f)
    ⟨QuotientGroup.kerLift_injective f, hsurj⟩
  have hli : ∀ x : (B.quotientToInvariants f.ker).V,
      (Rep.Hom.hom e) ((Rep.Hom.hom (inv e)) x) = x := by
    intro x
    have h := congrArg (fun (m : B.quotientToInvariants f.ker ⟶ B.quotientToInvariants f.ker) =>
      ⇑(Rep.Hom.hom m)) (IsIso.inv_hom_id e)
    rw [Rep.hom_comp, Rep.hom_id] at h
    simpa using congr_fun h x
  have hri : ∀ y : A.V, (Rep.Hom.hom (inv e)) ((Rep.Hom.hom e) y) = y := by
    intro y
    have h := congrArg (fun (m : Rep.res (QuotientGroup.kerLift f) A ⟶
      Rep.res (QuotientGroup.kerLift f) A) => ⇑(Rep.Hom.hom m)) (IsIso.hom_inv_id e)
    rw [Rep.hom_comp, Rep.hom_id] at h
    simpa using congr_fun h y
  let e' : (B.quotientToInvariants f.ker).V ≃ₗ[k] A.V :=
    { toFun := ⇑(Rep.Hom.hom (inv e))
      invFun := ⇑(Rep.Hom.hom e)
      left_inv := hli
      right_inv := hri
      map_add' := fun x y => map_add (Rep.Hom.hom (inv e)) x y
      map_smul' := fun c x => map_smul (Rep.Hom.hom (inv e)) c x }
  have he : ∀ q : G ⧸ f.ker,
      (e' : (B.quotientToInvariants f.ker).V →ₗ[k] A.V) ∘ₗ (B.quotientToInvariants f.ker).ρ q
        = A.ρ (eH q) ∘ₗ (e' : (B.quotientToInvariants f.ker).V →ₗ[k] A.V) :=
    fun q => (Rep.Hom.hom (inv e)).isIntertwining' q
  have hinj_first : Function.Injective (groupCohomology.map (QuotientGroup.kerLift f) e 2).hom := by
    have hmap : groupCohomology.map (QuotientGroup.kerLift f) e 2
        = (groupCohomology.mapIso eH e' he 2).inv := by
      show groupCohomology.map (QuotientGroup.kerLift f) e 2
        = groupCohomology.map (eH : G ⧸ f.ker →* H)
            (Rep.ofHom ⟨e'.symm, _⟩) 2
      refine groupCohomology.map_congr rfl ?_ 2
      apply LinearMap.ext
      intro y
      rfl
    rw [hmap]
    exact (ConcreteCategory.bijective_of_isIso _).1
  have hinf : Function.Injective ((groupCohomology.infNatTrans k f.ker 2).app B).hom :=
    Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1_general
      f.ker B hB
  rw [hkey]
  exact hinf.comp hinj_first


theorem subsingleton_classesK_res_one (k L : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (S : Subgroup (L ≃ₐ[k] L)) :
    Subsingleton (groupCohomology (Rep.res S.subtype (SSGRoute.PTExt.classesK k L)) 1) := by
  have h1 : Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction ↥S (NK.GlobalCFT.IdeleClassGroup L)) 1) :=
    NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup S
  have h2 : Subsingleton (groupCohomology (Rep.ofDistribMulAction SSGRoute.PTExt.Coeff ↥S
      (Additive (NK.GlobalCFT.IdeleClassGroup L))) 1) :=
    NK.HassePrinciple.subsingleton_groupCohomology_one_of_mulCoboundary SSGRoute.PTExt.Coeff
      (NK.HassePrinciple.mulCoboundary_of_subsingleton_groupCohomology_one h1)
  exact h2

theorem classIncl_inj_surj_invariants (k F L : Type) [Field k] [NumberField k] [Field F]
    [NumberField F] [Field L] [NumberField L] [Algebra k F] [Algebra F L] [Algebra k L]
    [IsScalarTower k F L] [FiniteDimensional k F] [IsGalois k F] [FiniteDimensional k L]
    [IsGalois k L] :
    Function.Injective (SSGRoute.PTExt.classIncl k F L).hom ∧
    (∀ b : (SSGRoute.PTExt.classesK k L).V,
        (∀ s : (SSGRoute.PTExt.galRes k F L).ker,
          (SSGRoute.PTExt.classesK k L).ρ s.1 b = b) →
        ∃ a : (SSGRoute.PTExt.classesK k F).V,
          (SSGRoute.PTExt.classIncl k F L).hom a = b) := by
  classical
  haveI : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite k F L
  haveI : IsGalois F L := IsGalois.tower_top_of_isGalois k F L
  obtain ⟨u, hu, φ, hφ, hι⟩ := classIncl_isCanonical k F L
  obtain ⟨ψ, hψ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists u hu φ hφ
  have hclass' : ∀ q : IdeleClassGroup F,
      (SSGRoute.PTExt.classIncl k F L).hom (Additive.ofMul q) = Additive.ofMul (ψ q) := by
    intro q
    obtain ⟨x, rfl⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective F q
    exact (hι x).trans (congrArg Additive.ofMul (hψ x).symm)
  have hψinj : Function.Injective ψ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective u hu φ hφ ψ hψ
  constructor
  · intro a1 a2 h
    have h1 : Additive.ofMul (ψ (Additive.toMul a1)) = Additive.ofMul (ψ (Additive.toMul a2)) :=
      (hclass' (Additive.toMul a1)).symm.trans (h.trans (hclass' (Additive.toMul a2)))
    have h3 : Additive.ofMul (Additive.toMul a1) = Additive.ofMul (Additive.toMul a2) :=
      congrArg Additive.ofMul (hψinj (Additive.ofMul.injective h1))
    exact (ofMul_toMul a1).symm.trans (h3.trans (ofMul_toMul a2))
  · intro b hb
    set q : IdeleClassGroup L := Additive.toMul b with hq
    have hbq : ∀ τ : L ≃ₐ[F] L, τ • q = q := by
      intro τ
      have hσ : (AlgEquiv.restrictScalars k τ) ∈ (SSGRoute.PTExt.galRes k F L).ker := by
        rw [MonoidHom.mem_ker]
        apply AlgEquiv.ext
        intro x
        apply (algebraMap F L).injective
        show algebraMap F L ((AlgEquiv.restrictScalars k τ).restrictNormal F x) = algebraMap F L x
        rw [AlgEquiv.restrictNormal_commutes]
        exact AlgEquiv.commutes τ x
      have h1 : (AlgEquiv.restrictScalars k τ) • q = q :=
        Additive.ofMul.injective (hb ⟨AlgEquiv.restrictScalars k τ, hσ⟩)
      have h3 : (SSGRoute.PTExt.classesK k L).ρ (AlgEquiv.restrictScalarsHom k τ)
            (Additive.ofMul q)
          = (SSGRoute.PTExt.classesK F L).ρ τ (Additive.ofMul q) := by
        rw [NK.HassePrinciple.classGroupRep_ρ_apply, NK.HassePrinciple.classGroupRep_ρ_apply]
        congr 1
      exact (Additive.ofMul.injective h3.symm).trans h1
    have hmem : q ∈ ψ.range :=
      ((NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup u hu φ hφ ψ hψ q).mp hbq)
    obtain ⟨c, hc⟩ := hmem
    refine ⟨Additive.ofMul c, ?_⟩
    show (SSGRoute.PTExt.classIncl k F L).hom (Additive.ofMul c) = b
    rw [hclass' c, hc]
    exact ofMul_toMul b



/-- **Injectivity of the level inflation on `H²`.** -/
theorem classIncl_inflation_injective (k F L : Type) [Field k] [NumberField k] [Field F]
    [NumberField F] [Field L] [NumberField L] [Algebra k F] [Algebra F L] [Algebra k L]
    [IsScalarTower k F L] [FiniteDimensional k F] [IsGalois k F] [FiniteDimensional k L]
    [IsGalois k L] :
    Function.Injective (fun y : groupCohomology (SSGRoute.PTExt.classesK k F) 2 =>
      (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
        (SSGRoute.PTExt.classIncl k F L) 2).hom y) := by
  have hsurj : Function.Surjective (SSGRoute.PTExt.galRes k F L) :=
    AlgEquiv.restrictNormalHom_surjective L
  obtain ⟨hinj, hsurj'⟩ := classIncl_inj_surj_invariants k F L
  exact H2_map_injective_of_ker_coeff (SSGRoute.PTExt.galRes k F L) hsurj
    (SSGRoute.PTExt.classesK k F) (SSGRoute.PTExt.classesK k L) (SSGRoute.PTExt.classIncl k F L)
    hinj hsurj' (subsingleton_classesK_res_one k L (SSGRoute.PTExt.galRes k F L).ker)

end Work.SSGRoute

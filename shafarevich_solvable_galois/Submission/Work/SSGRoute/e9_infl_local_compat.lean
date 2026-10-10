import Mathlib.Tactic.Have
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.decompK_restrict_surjective
import Submission.Work.SSGRoute.e6_util
import Submission.Work.SSGRoute.eCoh_map
import Submission.Work.SSGRoute.inflCIn_trans
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped NumberField
open CategoryTheory SSGRoute.PTExt

/-! ## The two abstract inputs

Both are completely independent of the arithmetic setting: the first is a statement about Mathlib's
`groupCohomology`, the second transports it to the `Ext` core of `SSGRoute.PTExt` along the `E0b`
bridge `eCoh`. -/

/-- **Inflation along a surjection is injective in degree `1` (group-cohomology model).**  For a
surjective group homomorphism `f : H ↠ G` and a `G`-module `A`, the change-of-group map
`H¹(G, A) → H¹(H, res_f A)` — which on `1`-cocycles is precomposition with `f` — is injective.  A
`1`-cocycle `z` on `G` whose pullback is a coboundary `h ↦ (res_f A)(h) a - a` has
`z (f h) = A (f h) a - a`, and every `g : G` is `f h` for some `h`, so `z` is that same coboundary
on `G`. -/
theorem e9_groupCohomology_map_id_injective_H1 {k G H : Type} [CommRing k] [Group G] [Group H]
    (f : H →* G) (hf : Function.Surjective f) (A : Rep k G) :
    Function.Injective
      ((groupCohomology.map f (𝟙 (Rep.res f A)) 1).hom) := by
  have key : ∀ w : groupCohomology A 1,
      (groupCohomology.map f (𝟙 (Rep.res f A)) 1).hom w = 0 → w = 0 := by
    intro w hw
    induction w using groupCohomology.H1_induction_on with
    | h z =>
      have hcoe : ⇑((ConcreteCategory.hom (groupCohomology.mapCocycles₁ f
          (𝟙 (Rep.res f A)))) z) = fun h : H => z (f h) := by
        funext h
        rw [groupCohomology.coe_mapCocycles₁]
        rfl
      rw [groupCohomology.H1π_comp_map_apply f (𝟙 (Rep.res f A)) z] at hw
      rw [groupCohomology.H1π_eq_zero_iff] at hw
      rw [hcoe] at hw
      rw [groupCohomology.coboundaries₁, LinearMap.mem_range] at hw
      obtain ⟨a, ha⟩ := hw
      rw [groupCohomology.H1π_eq_zero_iff, groupCohomology.coboundaries₁, LinearMap.mem_range]
      refine ⟨a, ?_⟩
      funext g
      obtain ⟨h, rfl⟩ := hf g
      have h' := congrFun ha h
      rw [groupCohomology.d₀₁_hom_apply] at h' ⊢
      exact h'
  intro x y hxy
  have h0 := key (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp h0

/-- **Inflation along a surjection is injective in degree `1` (`Ext` core).**  Transport of
`e9_groupCohomology_map_id_injective_H1` along the `E0b` bridge `eCoh` (`Work.SSGRoute.eCoh_map`
is the naturality square of `eCoh` under a change of group, and `eCoh` is an additive equivalence
in every degree). -/
theorem e9_extHMap_id_injective_H1 {G H : Type} [Group G] [Group H] (f : H →* G)
    (A : Rep Coeff G)
    (h : Function.Injective ((groupCohomology.map f (𝟙 (Rep.res f A)) 1).hom)) :
    Function.Injective (fun y : extH A 1 => extHMap f (𝟙 (Rep.res f A)) y) := by
  intro x y hxy
  have hx : (SSGRoute.PTExt.eCoh 1 G A).symm x = (SSGRoute.PTExt.eCoh 1 G A).symm y := by
    apply h
    apply (SSGRoute.PTExt.eCoh 1 H (Rep.res f A)).injective
    rw [eCoh_map 1 G H f A (Rep.res f A) (𝟙 (Rep.res f A)) ((SSGRoute.PTExt.eCoh 1 G A).symm x),
      eCoh_map 1 G H f A (Rep.res f A) (𝟙 (Rep.res f A)) ((SSGRoute.PTExt.eCoh 1 G A).symm y),
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact hxy
  exact (SSGRoute.PTExt.eCoh 1 G A).symm.injective hx

/-! ## Restriction of a group homomorphism to a pair of subgroups -/

/-- The restriction `D' → D` of a group homomorphism `φ : G →* H` sending `D' ≤ G` into `D ≤ H`. -/
def restrictHom {G H : Type} [Group G] [Group H] (φ : G →* H) (D' : Subgroup G) (D : Subgroup H)
    (hmem : ∀ σ : G, σ ∈ D' → φ σ ∈ D) : D' →* D where
  toFun σ := ⟨φ (σ : G), hmem (σ : G) σ.2⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' σ τ := Subtype.ext (map_mul φ (σ : G) (τ : G))

theorem restrictHom_apply {G H : Type} [Group G] [Group H] (φ : G →* H) (D' : Subgroup G)
    (D : Subgroup H) (hmem : ∀ σ : G, σ ∈ D' → φ σ ∈ D) (σ : D') :
    ((restrictHom φ D' D hmem σ : D) : H) = φ (σ : G) := rfl

/-- **Restriction commutes with inflation (abstract form).**  For a group homomorphism
`φ : G →* H`, subgroups `D' ≤ G`, `D ≤ H` with `φ '' D' ⊆ D`, an `H`-module `M` and a class
`y ∈ Hⁿ(H, M)`,
`extHRestrict D' (extHMap φ id y) = extHMap f id (extHRestrict D y)`
where `f = restrictHom φ D' D hmem` is the restriction of `φ` to `D' → D`.  Both sides compute the
change-of-group map along the common homomorphism `φ.comp D'.subtype = D.subtype.comp f`, the first
by transitivity of `extHMap` (`Work.SSGRoute.extHMap_comp_aux`), the second likewise. -/
theorem extHRestrict_extHMap_eq {G H : Type} [Group G] [Group H] (φ : G →* H) (D' : Subgroup G)
    (D : Subgroup H) (hmem : ∀ σ : G, σ ∈ D' → φ σ ∈ D) (M : Rep Coeff H) {n : ℕ}
    (y : extH M n) :
    extHRestrict D' (extHMap φ (𝟙 (Rep.res φ M)) y)
      = extHMap (restrictHom φ D' D hmem) (𝟙 _) (extHRestrict D y) := by
  have h1 : extHRestrict D' (extHMap φ (𝟙 (Rep.res φ M)) y)
      = extHMap (φ.comp D'.subtype) (𝟙 (Rep.res (φ.comp D'.subtype) M)) y := by
    rw [extHRestrict]
    refine extHMap_comp_aux φ D'.subtype (𝟙 (Rep.res φ M))
      (𝟙 (Rep.res D'.subtype (Rep.res φ M))) (𝟙 (Rep.res (φ.comp D'.subtype) M)) ?_ y
    rw [show Rep.resMap D'.subtype (𝟙 (Rep.res φ M)) = 𝟙 (Rep.res D'.subtype (Rep.res φ M))
        from by
      change (Rep.resFunctor D'.subtype).map (𝟙 (Rep.res φ M)) = _
      rw [CategoryTheory.Functor.map_id]]
    rw [Category.id_comp]
    rfl
  have h2 : extHMap (restrictHom φ D' D hmem)
        (𝟙 (Rep.res (restrictHom φ D' D hmem) (Rep.res D.subtype M))) (extHRestrict D y)
      = extHMap (D.subtype.comp (restrictHom φ D' D hmem))
          (𝟙 (Rep.res (D.subtype.comp (restrictHom φ D' D hmem)) M)) y := by
    rw [extHRestrict]
    refine extHMap_comp_aux D.subtype (restrictHom φ D' D hmem) (𝟙 (Rep.res D.subtype M))
      (𝟙 (Rep.res (restrictHom φ D' D hmem) (Rep.res D.subtype M)))
      (𝟙 (Rep.res (D.subtype.comp (restrictHom φ D' D hmem)) M)) ?_ y
    rw [show Rep.resMap (restrictHom φ D' D hmem) (𝟙 (Rep.res D.subtype M))
          = 𝟙 (Rep.res (restrictHom φ D' D hmem) (Rep.res D.subtype M)) from by
      change (Rep.resFunctor (restrictHom φ D' D hmem)).map (𝟙 (Rep.res D.subtype M)) = _
      rw [CategoryTheory.Functor.map_id]]
    rw [Category.id_comp]
    rfl
  exact h1.trans ((rfl : extHMap (φ.comp D'.subtype) (𝟙 (Rep.res (φ.comp D'.subtype) M)) y
      = extHMap (D.subtype.comp (restrictHom φ D' D hmem))
          (𝟙 (Rep.res (D.subtype.comp (restrictHom φ D' D hmem)) M)) y).trans h2.symm)

/-! ## The main statement -/

/-- Lifting an inflated class `inflH h'` at the level `L ⊇ K`, vanishing at the decomposition
group of a place `w'` of `L` is equivalent to vanishing of `h'` at the decomposition group of the
place `v` of `K` below: `D_{w'} → D_v` is surjective (`decompK_restrict_surjective`) and inflation
along it is injective (the kernel lies in `Gal(L/K)`, on which `M` is trivial, but in fact
injectivity of the degree-`1` inflation only needs surjectivity).  Route: naturality of `extHMap`
gives `extHRestrict D_{w'} (inflH h') = extHMap f 𝟙 (extHRestrict D_v h')` for the surjection
`f : D_{w'} →* D_v` with `f σ = galRes σ`; `⟸` is immediate, and `⟹` needs `f` to be injective on
`H¹` (inflation along a surjection is injective in degree `1`). -/
theorem e9_infl_local_compat (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (h' : extH M 1) :
    ∀ (v : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L),
      NK.GlobalCFT.Place.LiesOver w' v →
      (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (inflH (k := k) (K := K) (L := L) h') = 0 ↔
        extHRestrict (MulAction.stabilizer (K ≃ₐ[k] K) v) h' = 0) := by
  intro v w' hw'
  -- The restriction map `D_{w'} → D_v` along `galRes`.
  have hmem : ∀ σ : L ≃ₐ[k] L, σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) w' →
      galRes k K L σ ∈ MulAction.stabilizer (K ≃ₐ[k] K) v := by
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff] at hσ ⊢
    have hlies0 : NK.GlobalCFT.Place.LiesOver (σ • w') (galRes k K L σ • v) :=
      NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := L) σ (galRes k K L σ)
        (fun y => AlgEquiv.restrictNormal_commutes σ K y) hw'
    rw [hσ] at hlies0
    exact NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique hlies0 hw'
  let f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* MulAction.stabilizer (K ≃ₐ[k] K) v :=
    restrictHom (galRes k K L) _ _ hmem
  have hfsub : ∀ σ : MulAction.stabilizer (L ≃ₐ[k] L) w',
      ((f σ : MulAction.stabilizer (K ≃ₐ[k] K) v) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L) :=
    fun σ => rfl
  have hsurj : Function.Surjective f := decompK_restrict_surjective k K v L w' hw' f hfsub
  have hinj : Function.Injective
      (fun y : extH (Rep.res (MulAction.stabilizer (K ≃ₐ[k] K) v).subtype M) 1 =>
        extHMap f (𝟙 (Rep.res f (Rep.res (MulAction.stabilizer (K ≃ₐ[k] K) v).subtype M))) y) :=
    e9_extHMap_id_injective_H1 f (Rep.res (MulAction.stabilizer (K ≃ₐ[k] K) v).subtype M)
      (e9_groupCohomology_map_id_injective_H1 f hsurj
        (Rep.res (MulAction.stabilizer (K ≃ₐ[k] K) v).subtype M))
  have hkey : extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (inflH (k := k) (K := K) (L := L) h')
      = extHMap f (𝟙 (Rep.res f (Rep.res (MulAction.stabilizer (K ≃ₐ[k] K) v).subtype M)))
          (extHRestrict (MulAction.stabilizer (K ≃ₐ[k] K) v) h') := by
    rw [show inflH (k := k) (K := K) (L := L) h'
        = extHMap (galRes k K L) (𝟙 (Rep.res (galRes k K L) M)) h' from rfl]
    exact extHRestrict_extHMap_eq (galRes k K L) (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (MulAction.stabilizer (K ≃ₐ[k] K) v) hmem M h'
  constructor
  · intro h0
    have h1 : extHMap f (𝟙 (Rep.res f (Rep.res (MulAction.stabilizer (K ≃ₐ[k] K) v).subtype M)))
        (extHRestrict (MulAction.stabilizer (K ≃ₐ[k] K) v) h') = 0 := by
      rw [← hkey]; exact h0
    have h2 : extHMap f (𝟙 (Rep.res f (Rep.res (MulAction.stabilizer (K ≃ₐ[k] K) v).subtype M)))
        (extHRestrict (MulAction.stabilizer (K ≃ₐ[k] K) v) h')
        = extHMap f (𝟙 (Rep.res f (Rep.res (MulAction.stabilizer (K ≃ₐ[k] K) v).subtype M))) 0 :=
      h1.trans (E6Util.extHMap_zero f _).symm
    exact hinj h2
  · intro h0
    have h2 : extHMap f (𝟙 (Rep.res f (Rep.res (MulAction.stabilizer (K ≃ₐ[k] K) v).subtype M)))
        (extHRestrict (MulAction.stabilizer (K ≃ₐ[k] K) v) h') = 0 := by
      rw [h0]
      exact E6Util.extHMap_zero f _
    exact hkey.trans h2

end Work.SSGRoute

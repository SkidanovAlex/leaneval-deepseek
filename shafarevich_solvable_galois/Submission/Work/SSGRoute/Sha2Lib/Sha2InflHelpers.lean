import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.glue_involution_place
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.Sha2Lib

/-- The pullback of a `1`-cocycle along a group homomorphism. -/
noncomputable def pullbackCocycles₁ {k : Type} [CommRing k] {Γ Q : Type} [Group Γ] [Group Q]
    (f : Γ →* Q) (A : Rep.{0} k Q) (z : ↥(groupCohomology.cocycles₁ A)) :
    ↥(groupCohomology.cocycles₁ (Rep.res f A)) :=
  ⟨fun x => z (f x), by
    rw [groupCohomology.mem_cocycles₁_iff]
    have hz : ∀ x y : Q, z (x * y) = A.ρ x (z y) + z x :=
      fun x y => (groupCohomology.mem_cocycles₁_iff (z : Q → ↥A)).mp z.2 x y
    intro a b
    show z (f (a * b)) = ((Rep.res f A).ρ a) (z (f b)) + z (f a)
    rw [map_mul]
    exact hz (f a) (f b)⟩

@[simp] lemma pullbackCocycles₁_apply {k : Type} [CommRing k] {Γ Q : Type} [Group Γ] [Group Q]
    (f : Γ →* Q) (A : Rep.{0} k Q) (z : ↥(groupCohomology.cocycles₁ A)) (x : Γ) :
    (pullbackCocycles₁ f A z : Γ → ↥(Rep.res f A)) x = (z : Q → ↥A) (f x) := rfl

/-- The pullback identity: inflating the class of `zQ` gives the class of the pullback cocycle. -/
theorem map_H1pi_eq_of_comp {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]
    (f : G →* H) (A : Rep.{0} k H) (zQ : ↥(groupCohomology.cocycles₁ A))
    (zL : ↥(groupCohomology.cocycles₁ (Rep.res f A)))
    (h : ∀ x : G, (zL : G → ↥(Rep.res f A)) x = (zQ : H → ↥A) (f x)) :
    CategoryTheory.ConcreteCategory.hom
        (groupCohomology.map f (CategoryTheory.CategoryStruct.id (Rep.res f A)) 1)
        (CategoryTheory.ConcreteCategory.hom (groupCohomology.H1π A) zQ)
      = CategoryTheory.ConcreteCategory.hom (groupCohomology.H1π (Rep.res f A)) zL := by
  rw [groupCohomology.H1π_comp_map_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro x
  rw [groupCohomology.coe_mapCocycles₁]
  simp only [groupCohomology.cochainsMap₁]
  exact (h x).symm

/-- The group-change of `H¹` kills a class iff its pullback cocycle is a coboundary. -/
theorem map_H1pi_eq_zero_iff_exists_coboundary {k : Type} [CommRing k] {G H : Type} [Group G]
    [Group H] (f : G →* H) (A : Rep.{0} k H) (zQ : ↥(groupCohomology.cocycles₁ A))
    (zL : ↥(groupCohomology.cocycles₁ (Rep.res f A)))
    (hzL : ∀ x : G, (zL : G → ↥(Rep.res f A)) x = (zQ : H → ↥A) (f x)) :
    (CategoryTheory.ConcreteCategory.hom
        (groupCohomology.map f (CategoryTheory.CategoryStruct.id (Rep.res f A)) 1)
        (CategoryTheory.ConcreteCategory.hom (groupCohomology.H1π A) zQ) = 0) ↔
      ∃ m : ↥(Rep.res f A), ∀ x : G, (zL : G → ↥(Rep.res f A)) x
        = (Rep.res f A).ρ x m - m := by
  have hmap : CategoryTheory.ConcreteCategory.hom
        (groupCohomology.map f (CategoryTheory.CategoryStruct.id (Rep.res f A)) 1)
        (CategoryTheory.ConcreteCategory.hom (groupCohomology.H1π A) zQ)
      = CategoryTheory.ConcreteCategory.hom (groupCohomology.H1π (Rep.res f A)) zL :=
    map_H1pi_eq_of_comp f A zQ zL hzL
  rw [hmap]
  constructor
  · intro h0
    rw [groupCohomology.H1π_eq_zero_iff] at h0
    change (zL : G → ↥(Rep.res f A)) ∈ groupCohomology.coboundaries₁ (Rep.res f A) at h0
    rw [show groupCohomology.coboundaries₁ (Rep.res f A)
        = LinearMap.range (groupCohomology.d₀₁ (Rep.res f A)).hom from rfl] at h0
    rw [LinearMap.mem_range] at h0
    obtain ⟨m, hm⟩ := h0
    refine ⟨m, fun x => ?_⟩
    have h2 := congrFun hm x
    rw [groupCohomology.d₀₁_hom_apply] at h2
    exact h2.symm
  · rintro ⟨m, hm⟩
    rw [groupCohomology.H1π_eq_zero_iff]
    change (zL : G → ↥(Rep.res f A)) ∈ groupCohomology.coboundaries₁ (Rep.res f A)
    rw [show groupCohomology.coboundaries₁ (Rep.res f A)
        = LinearMap.range (groupCohomology.d₀₁ (Rep.res f A)).hom from rfl]
    rw [LinearMap.mem_range]
    refine ⟨m, funext fun x => ?_⟩
    rw [groupCohomology.d₀₁_hom_apply]
    exact (hm x).symm

/-- The stabiliser of an archimedean place is trivial or consists of two elements. -/
theorem infinite_place_stabilizer_trivial_or_two (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (v : NumberField.InfinitePlace K) :
    MulAction.stabilizer (K ≃ₐ[k] K) v = ⊥ ∨
      ∃ c : K ≃ₐ[k] K, ∀ τ : K ≃ₐ[k] K,
        (τ ∈ MulAction.stabilizer (K ≃ₐ[k] K) v ↔ τ = 1 ∨ τ = c) := by
  rcases NumberField.InfinitePlace.isUnramified_or_isRamified k v with h | h
  · exact Or.inl (NumberField.InfinitePlace.IsUnramified.stabilizer_eq_bot (k := k) h)
  · refine Or.inr ?_
    obtain ⟨σ, hσ⟩ :=
      NumberField.InfinitePlace.exists_isConj_of_isRamified (φ := v.embedding) (by
        rwa [NumberField.InfinitePlace.mk_embedding v])
    refine ⟨σ, fun τ => ?_⟩
    have hset : (MulAction.stabilizer (K ≃ₐ[k] K)
        (NumberField.InfinitePlace.mk v.embedding) : Set (K ≃ₐ[k] K)) = {1, σ} :=
      hσ.coe_stabilizer_mk
    rw [NumberField.InfinitePlace.mk_embedding v] at hset
    rw [← SetLike.mem_coe, hset, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Surjectivity of the decomposition-group restriction at a finite place. -/
theorem decomp_group_restrict_surjective
    (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : (q'.asIdeal).LiesOver q.asIdeal)
    (τ : K ≃ₐ[k] K) (hτ : τ ∈ MulAction.stabilizer (K ≃ₐ[k] K) (NK.GlobalCFT.Place.ofFinite q)) :
    ∃ σ : L ≃ₐ[k] L,
      σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q') ∧
        SSGRoute.PTExt.galRes k K L σ = τ := by
  classical
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois k K L
  have hlies : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite q) :=
    (place_liesOver_ofFinite_iff q' (NK.GlobalCFT.Place.ofFinite q)).mpr ⟨q, rfl, h⟩
  have hsurj : Function.Surjective (SSGRoute.PTExt.galRes k K L) :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := L)
  obtain ⟨σ₀, hσ₀⟩ := hsurj τ
  have hlies₁ : NK.GlobalCFT.Place.LiesOver (σ₀ • NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite q) := by
    have h1 := NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := L) σ₀
      (SSGRoute.PTExt.galRes k K L σ₀) (fun y => AlgEquiv.restrictNormal_commutes σ₀ K y) hlies
    rw [hσ₀, MulAction.mem_stabilizer_iff.mp hτ] at h1
    exact h1
  obtain ⟨n, hn⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := K)
    hlies₁ hlies
  refine ⟨(AlgEquiv.restrictScalars k n) * σ₀, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul]
    rw [show AlgEquiv.restrictScalars k n • (σ₀ • NK.GlobalCFT.Place.ofFinite q')
        = n • (σ₀ • NK.GlobalCFT.Place.ofFinite q') from rfl, hn]
  · rw [map_mul]
    have h1 : SSGRoute.PTExt.galRes k K L (AlgEquiv.restrictScalars k n) = 1 := by
      ext y
      apply (algebraMap K L).injective
      change (algebraMap K L)
          ((AlgEquiv.restrictNormal (AlgEquiv.restrictScalars k n) K) y)
        = (algebraMap K L) ((1 : K ≃ₐ[k] K) y)
      rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
      change n (algebraMap K L y) = algebraMap K L y
      exact AlgEquiv.commutes n y
    rw [h1, one_mul]
    exact hσ₀

end Work.SSGRoute.Sha2Lib

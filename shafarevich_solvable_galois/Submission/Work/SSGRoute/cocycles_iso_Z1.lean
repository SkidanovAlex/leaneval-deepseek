import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Z¹(G, A) ⧸ B¹(G, A)` depends only on the underlying `ℤ[G]`-module

Degree-`1` companion of `Work.SSGRoute.cocycles_iso_Z2`.
-/

open CategoryTheory

namespace Work.SSGRoute

/-- **`Z¹(G, A) ⧸ B¹(G, A)` depends only on the underlying `ℤ[G]`-module.**  Degree-`1` companion of
`Work.SSGRoute.cocycles_iso_Z2`: for `A : Rep k G` and an additive commutative group `M` with a
`DistribMulAction` of `G`, together with an additive equivalence `φ : A.V ≃+ M` commuting with the
actions (`φ (A.ρ g v) = g • φ v`), transporting coefficients along `φ` (`f ↦ φ ∘ f`) carries
Mathlib's `1`-cocycles `cocycles₁ A` onto the crossed homomorphisms `Z1 G M` of
`Work.GroupCohomology` and the `1`-coboundaries `coboundaries₁ A` onto `B1 G M`, giving an additive
isomorphism of the quotients, i.e. of `H¹(G, A)` with `Work.GroupCohomology.H1 G M`.  Only
additivity and `G`-equivariance of `φ` are used, since the differentials `d₀₁` (`d0`) and `d₁₂`
(`d1`) involve only the action and the additive structure. -/
theorem cocycles_iso_Z1 (k G : Type) [CommRing k] [Group G]
    (A : Rep.{0} k G) (M : Type) [AddCommGroup M] [DistribMulAction G M]
    (φ : A.V ≃+ M) (hφ : ∀ (g : G) (v : A.V), φ (A.ρ g v) = g • φ v) :
    Nonempty (((groupCohomology.cocycles₁ A) ⧸
        ((groupCohomology.coboundaries₁ A).comap (groupCohomology.cocycles₁ A).subtype))
      ≃+ Work.GroupCohomology.H1 G M) := by
  let eG : (G → A.V) ≃+ (G → M) := AddEquiv.piCongrRight (fun _ => φ)
  let eGG : (G × G → A.V) ≃+ (G × G → M) := AddEquiv.piCongrRight (fun _ => φ)
  have heG : ∀ (f : G → A.V) (g : G), eG f g = φ (f g) := fun _ _ => rfl
  have heGG : ∀ (c : G × G → A.V) (p : G × G), eGG c p = φ (c p) := fun _ _ => rfl
  -- the transported differential
  have hd : ∀ f : A.V,
      eG ((groupCohomology.d₀₁ A).hom f) = Work.GroupCohomology.d0 G M (φ f) := by
    intro f
    funext g
    simp only [heG, groupCohomology.d₀₁_hom_apply, Work.GroupCohomology.d0_apply]
    rw [map_sub, hφ]
  -- cocycles correspond
  have hcyc : ∀ c : G → A.V,
      c ∈ groupCohomology.cocycles₁ A ↔ eG c ∈ Work.GroupCohomology.Z1 G M := by
    intro c
    rw [groupCohomology.mem_cocycles₁_iff, Work.GroupCohomology.mem_Z1_iff]
    constructor
    · intro hc g h
      simp only [heG]
      rw [hc g h, map_add, hφ]
    · intro hc g h
      refine φ.injective ?_
      have h1 := hc g h
      simp only [heG] at h1
      rw [← hφ, ← map_add] at h1
      exact h1
  -- coboundaries correspond
  have hcob : ∀ c : G → A.V,
      c ∈ groupCohomology.coboundaries₁ A ↔ eG c ∈ Work.GroupCohomology.B1 G M := by
    intro c
    rw [Work.GroupCohomology.mem_B1_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨φ a, (hd a).symm⟩
    · rintro ⟨m, hm⟩
      refine ⟨φ.symm m, ?_⟩
      apply eG.injective
      rw [hd, AddEquiv.apply_symm_apply]
      exact hm
  -- the cocycle-level additive equivalence
  let eC : (groupCohomology.cocycles₁ A) ≃+ Work.GroupCohomology.Z1 G M :=
    { toFun := fun c => ⟨eG c, (hcyc c).mp c.2⟩
      invFun := fun c => ⟨eG.symm c, (hcyc _).mpr (by
        rw [AddEquiv.apply_symm_apply]; exact c.2)⟩
      left_inv := fun c => Subtype.ext (eG.symm_apply_apply (c : G → A.V))
      right_inv := fun c => Subtype.ext (eG.apply_symm_apply (c : G → M))
      map_add' := fun c c' => Subtype.ext (eG.map_add (c : G → A.V) (c' : G → A.V)) }
  refine ⟨QuotientAddGroup.congr
    (((groupCohomology.coboundaries₁ A).comap
      (groupCohomology.cocycles₁ A).subtype).toAddSubgroup)
    ((Work.GroupCohomology.B1 G M).comap (Work.GroupCohomology.Z1 G M).subtype)
    eC ?_⟩
  ext x
  constructor
  · intro hx
    rw [AddSubgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [AddSubgroup.mem_comap]
    show eG (y : G → A.V) ∈ Work.GroupCohomology.B1 G M
    have hy' : (y : G → A.V) ∈ groupCohomology.coboundaries₁ A := by
      simpa [Submodule.mem_toAddSubgroup, Submodule.mem_comap] using hy
    exact (hcob _).mp hy'
  · intro hx
    rw [AddSubgroup.mem_map]
    rw [AddSubgroup.mem_comap] at hx
    refine ⟨⟨eG.symm (x : G → M), (hcyc _).mpr (by
      rw [AddEquiv.apply_symm_apply]; exact x.2)⟩, ?_, ?_⟩
    · rw [Submodule.mem_toAddSubgroup, Submodule.mem_comap]
      exact (hcob (eG.symm (x : G → M))).mpr (by
        rw [AddEquiv.apply_symm_apply]; exact hx)
    · exact Subtype.ext (eG.apply_symm_apply (x : G → M))

end Work.SSGRoute

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Z²(G, A) ⧸ B²(G, A)` depends only on the underlying `ℤ[G]`-module

Let `A : Rep k G` and let `M` be an additive commutative group with a `DistribMulAction` of `G`,
together with an additive equivalence `φ : A.V ≃+ M` commuting with the actions,
`φ (A.ρ g v) = g • φ v`.  Transporting the coefficients along `φ` (`f ↦ φ ∘ f`) carries Mathlib's
`2`-cocycles `cocycles₂ A` onto the cocycles `Z2 G M` of `Submission.Work.GroupCohomology.Basic`
and the `2`-coboundaries `coboundaries₂ A` onto `B2 G M`; hence an additive isomorphism of the
quotients, i.e. of `H²(G, A)` with `Work.GroupCohomology.H2 G M`.

The differentials `d₁₂` (`d1`) and `d₂₃` (`d2`) involve only the action and the additive structure,
so nothing beyond additivity and `G`-equivariance of `φ` is used.
-/

open CategoryTheory

namespace Work.SSGRoute

theorem cocycles_iso_Z2 (k G : Type) [CommRing k] [Group G]
    (A : Rep.{0} k G) (M : Type) [AddCommGroup M] [DistribMulAction G M]
    (φ : A.V ≃+ M) (hφ : ∀ (g : G) (v : A.V), φ (A.ρ g v) = g • φ v) :
    Nonempty (((groupCohomology.cocycles₂ A) ⧸
        ((groupCohomology.coboundaries₂ A).comap (groupCohomology.cocycles₂ A).subtype))
      ≃+ Work.GroupCohomology.H2 G M) := by
  let eGG : (G × G → A.V) ≃+ (G × G → M) := AddEquiv.piCongrRight (fun _ => φ)
  let eG : (G → A.V) ≃+ (G → M) := AddEquiv.piCongrRight (fun _ => φ)
  have heGG : ∀ (c : G × G → A.V) (p : G × G), eGG c p = φ (c p) := fun _ _ => rfl
  have heG : ∀ (f : G → A.V) (g : G), eG f g = φ (f g) := fun _ _ => rfl
  -- the transported differential
  have hd : ∀ f : G → A.V,
      eGG ((groupCohomology.d₁₂ A).hom f) = Work.GroupCohomology.d1 G M (eG f) := by
    intro f
    funext p
    obtain ⟨g, h⟩ := p
    simp only [heGG, heG, groupCohomology.d₁₂_hom_apply, Work.GroupCohomology.d1_apply]
    rw [map_add, map_sub, hφ]
  -- cocycles correspond
  have hcyc : ∀ c : G × G → A.V,
      c ∈ groupCohomology.cocycles₂ A ↔ eGG c ∈ Work.GroupCohomology.Z2 G M := by
    intro c
    rw [groupCohomology.mem_cocycles₂_iff, Work.GroupCohomology.mem_Z2_iff]
    constructor
    · intro hc g h j
      simp only [heGG]
      rw [← map_add, hc g h j, map_add, hφ]
    · intro hc g h j
      refine φ.injective ?_
      have h1 := hc g h j
      simp only [heGG] at h1
      rw [← map_add, ← hφ, ← map_add] at h1
      exact h1
  -- coboundaries correspond
  have hcob : ∀ c : G × G → A.V,
      c ∈ groupCohomology.coboundaries₂ A ↔ eGG c ∈ Work.GroupCohomology.B2 G M := by
    intro c
    rw [Work.GroupCohomology.mem_B2_iff]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨eG f, (hd f).symm⟩
    · rintro ⟨f', hf'⟩
      refine ⟨eG.symm f', ?_⟩
      apply eGG.injective
      rw [hd, AddEquiv.apply_symm_apply]
      exact hf'
  -- the cocycle-level additive equivalence
  let eC : (groupCohomology.cocycles₂ A) ≃+ Work.GroupCohomology.Z2 G M :=
    { toFun := fun c => ⟨eGG c, (hcyc c).mp c.2⟩
      invFun := fun c => ⟨eGG.symm c, (hcyc _).mpr (by
        rw [AddEquiv.apply_symm_apply]; exact c.2)⟩
      left_inv := fun c => Subtype.ext (eGG.symm_apply_apply (c : G × G → A.V))
      right_inv := fun c => Subtype.ext (eGG.apply_symm_apply (c : G × G → M))
      map_add' := fun c c' => Subtype.ext (eGG.map_add (c : G × G → A.V) (c' : G × G → A.V)) }
  refine ⟨QuotientAddGroup.congr
    (((groupCohomology.coboundaries₂ A).comap
      (groupCohomology.cocycles₂ A).subtype).toAddSubgroup)
    ((Work.GroupCohomology.B2 G M).comap (Work.GroupCohomology.Z2 G M).subtype)
    eC ?_⟩
  ext x
  constructor
  · intro hx
    rw [AddSubgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [AddSubgroup.mem_comap]
    show eGG (y : G × G → A.V) ∈ Work.GroupCohomology.B2 G M
    have hy' : (y : G × G → A.V) ∈ groupCohomology.coboundaries₂ A := by
      simpa [Submodule.mem_toAddSubgroup, Submodule.mem_comap] using hy
    exact (hcob _).mp hy'
  · intro hx
    rw [AddSubgroup.mem_map]
    rw [AddSubgroup.mem_comap] at hx
    refine ⟨⟨eGG.symm (x : G × G → M), (hcyc _).mpr (by
      rw [AddEquiv.apply_symm_apply]; exact x.2)⟩, ?_, ?_⟩
    · rw [Submodule.mem_toAddSubgroup, Submodule.mem_comap]
      exact (hcob (eGG.symm (x : G × G → M))).mpr (by
        rw [AddEquiv.apply_symm_apply]; exact hx)
    · exact Subtype.ext (eGG.apply_symm_apply (x : G × G → M))

end Work.SSGRoute

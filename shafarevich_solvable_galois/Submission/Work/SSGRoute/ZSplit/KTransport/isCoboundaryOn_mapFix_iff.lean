import Mathlib
import Submission.Work.SSGRoute.ZSplit.KTransport.Defs
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
import Submission.Work.SSGRoute.ZSplit.BaseChange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZSplit.KTransport

/-!
# The coboundary predicate transports along the base change `k → ↥K`

`mapFix k Ω K H hH` is the subgroup of `Gal(Ω/↥K)` corresponding to a subgroup `H ≤ G_k` contained
in `G_K = K.fixingSubgroup`, through `IntermediateField.fixingSubgroupEquiv K`.  This file shows
that `IsCoboundaryOn` agrees on the two sides, for a pair of cochains `f`, `f'` that correspond
under `fixingSubgroupEquiv` (`hag`).

The content is that on a subgroup of `G_K` the acting group `Gal(K/k)` is trivial
(`H ≤ K.fixingSubgroup = ker (res k K)`), and on the base-`↥K` side the acting group
`⊥ ≃ₐ[↥K] ⊥` is a subsingleton, so *both* coboundary conditions are simply the vanishing of the
cochain.  The equivalence of the two vanishing conditions is then the bijectivity of
`fixingSubgroupEquiv`, transported through `hag`.

This is the sibling of `isCocycleOn_mapFix_iff` and `isLocConstOn_mapFix_iff`, and it specializes
`Work.SSGRoute.isCoboundaryOn_fixingSubgroup_iff_zero_of_le` (which is stated with the extra
hypotheses `Fact p.Prime` and `SMulCommClass` that its argument does not use) to the base-`↥K`
side as well.
-/

theorem isCoboundaryOn_mapFix_iff (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (p : ℕ) [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H ≤ K.fixingSubgroup)
    (f : (Ω ≃ₐ[k] Ω) → ZMod p) (f' : (Ω ≃ₐ[↥K] Ω) → ZMod p)
    (hag : ∀ x : ↥(K.fixingSubgroup), f' (IntermediateField.fixingSubgroupEquiv K x)
      = f (x : Ω ≃ₐ[k] Ω)) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H f ↔
      SSGRoute.IsCoboundaryOn (SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω))
        (Work.SSGRoute.ZSplit.mapFix k Ω K H hH) f' := by
  -- On `H ≤ G_K` the acting group is trivial, so a coboundary is exactly a vanishing function.
  have key0 : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H f ↔ ∀ g ∈ H, f g = 0 := by
    constructor
    · rintro ⟨m, hm⟩ g hg
      have h1 : SSGRoute.res k K g = 1 := by
        rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := k)]
        exact hH hg
      rw [hm g hg, h1, one_smul, sub_self]
    · intro h
      refine ⟨0, fun g hg => ?_⟩
      rw [h g hg, smul_zero, sub_self]
  -- On the base-`↥K` side the acting group `⊥ ≃ₐ[↥K] ⊥` is a subsingleton, so likewise.
  have key1 : SSGRoute.IsCoboundaryOn
      (SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω))
      (Work.SSGRoute.ZSplit.mapFix k Ω K H hH) f' ↔
        ∀ g' ∈ Work.SSGRoute.ZSplit.mapFix k Ω K H hH, f' g' = 0 := by
    constructor
    · rintro ⟨m, hm⟩ g' hg'
      have h1 : SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω) g' = 1 :=
        Subsingleton.elim _ _
      rw [hm g' hg', h1, one_smul, sub_self]
    · intro h
      refine ⟨0, fun g' hg' => ?_⟩
      rw [h g' hg', smul_zero, sub_self]
  rw [key0, key1]
  -- It remains to compare the two vanishing conditions, through `fixingSubgroupEquiv`.
  constructor
  · intro hf g' hg'
    change g' ∈ (H.subgroupOf K.fixingSubgroup).map
      (IntermediateField.fixingSubgroupEquiv K) at hg'
    rw [Subgroup.mem_map] at hg'
    obtain ⟨x, hx, rfl⟩ := hg'
    rw [Subgroup.mem_subgroupOf] at hx
    change f' ((IntermediateField.fixingSubgroupEquiv K) x) = 0
    rw [hag x]
    exact hf _ hx
  · intro hf' g hg
    have hmem : (IntermediateField.fixingSubgroupEquiv K) ⟨g, hH hg⟩ ∈
        Work.SSGRoute.ZSplit.mapFix k Ω K H hH := by
      change (IntermediateField.fixingSubgroupEquiv K) ⟨g, hH hg⟩ ∈
        (H.subgroupOf K.fixingSubgroup).map (IntermediateField.fixingSubgroupEquiv K)
      rw [Subgroup.mem_map]
      exact ⟨⟨g, hH hg⟩, by rw [Subgroup.mem_subgroupOf]; exact hg, rfl⟩
    have h := hf' _ hmem
    rw [hag ⟨g, hH hg⟩] at h
    exact h

end Work.SSGRoute.ZSplit.KTransport

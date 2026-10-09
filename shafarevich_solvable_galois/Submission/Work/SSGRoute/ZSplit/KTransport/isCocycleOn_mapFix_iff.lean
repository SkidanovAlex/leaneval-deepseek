import Mathlib
import Submission.Work.SSGRoute.ZSplit.KTransport.Defs
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
import Submission.Work.SSGRoute.ZSplit.BaseChange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of the `1`-cocycle condition across the base change `k ↝ ↥K`

`Work.SSGRoute.ZSplit.mapFix k Ω K H hH` is the subgroup of `G_K = Ω ≃ₐ[↥K] Ω` corresponding to a
subgroup `H ≤ G_k` contained in `K.fixingSubgroup`, through the group isomorphism
`IntermediateField.fixingSubgroupEquiv K : K.fixingSubgroup ≃* (Ω ≃ₐ[↥K] Ω)`, which is the identity
on the underlying functions (`KTransport/Defs.lean`).

This file records that the `1`-cocycle condition on `H` transfers across that correspondence.  The
point is that *both* actions involved in the two cocycle conditions are trivial on the relevant
subgroup:

* on `H ≤ K.fixingSubgroup`, the restriction homomorphism `res k K = restrictNormalHom K` is
  `1` (its kernel is exactly `K.fixingSubgroup`);
* on the `↥K`-side the acting group is `↥⊥ ≃ₐ[↥K] ↥⊥`, which is a subsingleton, so its action on
  `ZMod p` is trivial.

Hence both sides of the equivalence are simply the statement that the (transported) cochain is
additive on the (transported) subgroup; the transport of the additivity statement is the
multiplicativity of `IntermediateField.fixingSubgroupEquiv K` together with the agreement
hypothesis `hag`.
-/

namespace Work.SSGRoute.ZSplit.KTransport

open _root_.SSGRoute

noncomputable section

section General

variable {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- If the action of `Γ` on `M` is trivial on a subgroup `H`, then the `1`-cocycle condition for
`f : Γ → M` on `H` is exactly additivity of `f` on `H`. -/
lemma isCocycleOn_iff_addOn (act : Γ →* G) (H : Subgroup Γ) (f : Γ → M)
    (hact : ∀ g ∈ H, act g = 1) :
    SSGRoute.IsCocycleOn act H f ↔ ∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + f h := by
  constructor
  · intro hf g hg h hh
    rw [hf g hg h hh, hact g hg, one_smul]
  · intro hf g hg h hh
    rw [hf g hg h hh, hact g hg, one_smul]

end General

theorem isCocycleOn_mapFix_iff (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H ≤ K.fixingSubgroup)
    (f : (Ω ≃ₐ[k] Ω) → ZMod p) (f' : (Ω ≃ₐ[↥K] Ω) → ZMod p)
    (hag : ∀ x : ↥(K.fixingSubgroup), f' (IntermediateField.fixingSubgroupEquiv K x)
      = f (x : Ω ≃ₐ[k] Ω)) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) H f ↔
      SSGRoute.IsCocycleOn (SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω))
        (Work.SSGRoute.ZSplit.mapFix k Ω K H hH) f' := by
  -- On `H ≤ K.fixingSubgroup` the restriction to `K` is trivial.
  have hker : ∀ g ∈ H, SSGRoute.res k K g = 1 := by
    intro g hg
    have : g ∈ (AlgEquiv.restrictNormalHom ↥K).ker := by
      rw [IntermediateField.restrictNormalHom_ker K]; exact hH hg
    simpa [SSGRoute.res] using this
  -- The acting group on the `↥K`-side is a subsingleton, so its action is trivial.
  have hker' : ∀ g ∈ Work.SSGRoute.ZSplit.mapFix k Ω K H hH,
      SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω) g = 1 :=
    fun g _ => Subsingleton.elim _ _
  -- Both sides are additivity statements, and these correspond through `fixingSubgroupEquiv`.
  have key : (∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + f h) ↔
      (∀ g ∈ Work.SSGRoute.ZSplit.mapFix k Ω K H hH,
        ∀ h ∈ Work.SSGRoute.ZSplit.mapFix k Ω K H hH, f' (g * h) = f' g + f' h) := by
    constructor
    · intro hf g hg h hh
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
      calc f' (K.fixingSubgroupEquiv x * K.fixingSubgroupEquiv y)
          = f' (K.fixingSubgroupEquiv (x * y)) := by rw [map_mul]
        _ = f ((x * y : ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω) := hag (x * y)
        _ = f ((x : Ω ≃ₐ[k] Ω) * (y : Ω ≃ₐ[k] Ω)) := by rw [Subgroup.coe_mul]
        _ = f (x : Ω ≃ₐ[k] Ω) + f (y : Ω ≃ₐ[k] Ω) :=
              hf _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)
        _ = f' (K.fixingSubgroupEquiv x) + f' (K.fixingSubgroupEquiv y) := by
              rw [hag x, hag y]
    · intro hf g hg h hh
      have hxmem : (⟨g, hH hg⟩ : ↥(K.fixingSubgroup)) ∈ H.subgroupOf K.fixingSubgroup := by
        rw [Subgroup.mem_subgroupOf]; exact hg
      have hymem : (⟨h, hH hh⟩ : ↥(K.fixingSubgroup)) ∈ H.subgroupOf K.fixingSubgroup := by
        rw [Subgroup.mem_subgroupOf]; exact hh
      have hfx : K.fixingSubgroupEquiv (⟨g, hH hg⟩ : ↥(K.fixingSubgroup)) ∈
          Work.SSGRoute.ZSplit.mapFix k Ω K H hH :=
        Subgroup.mem_map.mpr ⟨_, hxmem, rfl⟩
      have hfy : K.fixingSubgroupEquiv (⟨h, hH hh⟩ : ↥(K.fixingSubgroup)) ∈
          Work.SSGRoute.ZSplit.mapFix k Ω K H hH :=
        Subgroup.mem_map.mpr ⟨_, hymem, rfl⟩
      have hf' := hf _ hfx _ hfy
      calc f (g * h)
          = f ((↑((⟨g, hH hg⟩ : ↥(K.fixingSubgroup)) *
              (⟨h, hH hh⟩ : ↥(K.fixingSubgroup))) : Ω ≃ₐ[k] Ω)) := by simp
        _ = f' (K.fixingSubgroupEquiv ((⟨g, hH hg⟩ : ↥(K.fixingSubgroup)) * ⟨h, hH hh⟩)) :=
              (hag _).symm
        _ = f' (K.fixingSubgroupEquiv ⟨g, hH hg⟩ * K.fixingSubgroupEquiv ⟨h, hH hh⟩) := by
              rw [map_mul]
        _ = f' (K.fixingSubgroupEquiv ⟨g, hH hg⟩) + f' (K.fixingSubgroupEquiv ⟨h, hH hh⟩) := hf'
        _ = f g + f h := by rw [hag, hag]
  rw [isCocycleOn_iff_addOn (SSGRoute.res k K) H f hker,
      isCocycleOn_iff_addOn (SSGRoute.res (k := ↥K) (Ω := Ω) (⊥ : IntermediateField ↥K Ω))
        (Work.SSGRoute.ZSplit.mapFix k Ω K H hH) f' hker']
  exact key

end

end Work.SSGRoute.ZSplit.KTransport

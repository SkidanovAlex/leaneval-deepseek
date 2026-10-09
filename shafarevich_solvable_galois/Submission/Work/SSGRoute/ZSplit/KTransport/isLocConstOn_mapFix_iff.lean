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

open Filter Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Transport of local constancy along the base change `k ↝ ↥K`

`IsLocConstOn H f` (`SSGRoute.IsLocConstOn`, `Submission/Work/SSGRoute/Interfaces.lean`) says that
the cochain `f : G_k → M` is constant on the right `(U ∩ H)`-cosets of `H` for some open subgroup
`U ≤ G_k`.  For `H ≤ G_K` this predicate transports across the group isomorphism

  `IntermediateField.fixingSubgroupEquiv K : G_K ≃* Gal(Ω/↥K)`

which is the identity on the underlying functions: the open subgroups of `G_K` correspond, under
`fixingSubgroupEquiv K`, to the open subgroups of `Gal(Ω/↥K)` — the image of `Gal(Ω/M)`,
`K ≤ M`, being `Gal(Ω/kOver K M)`.

The file proves the transport in the *normal form* provided by the Krull topology: `IsLocConstOn`
is equivalent to the existence of a *finite-dimensional* intermediate field whose fixing subgroup
carries the constancy.  The two directions of the correspondence of finite subextensions,
`mapFix_fixingSubgroup_kOver` (a finite `Λ ≥ K` over `k` gives a finite `kOver K Λ` over `↥K`)
and `mapFix_fixingSubgroup_restrictScalars` (a finite `M` over `↥K` gives the finite
`M.restrictScalars k` over `k`), then yield the equivalence.
-/

section Helpers

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- `fixingSubgroupEquiv` is the identity on the underlying functions. -/
theorem fixingSubgroupEquiv_apply (x : ↥(K.fixingSubgroup)) (y : Ω) :
    ((IntermediateField.fixingSubgroupEquiv K) x : Ω ≃ₐ[↥K] Ω) y = (x : Ω ≃ₐ[k] Ω) y := rfl

/-- The inverse of `fixingSubgroupEquiv` is the identity on the underlying functions. -/
theorem fixingSubgroupEquiv_symm_apply (σ : Ω ≃ₐ[↥K] Ω) (y : Ω) :
    ((IntermediateField.fixingSubgroupEquiv K).symm σ : Ω ≃ₐ[k] Ω) y = σ y := rfl

/-- Membership in the fixing subgroup of the base change `kOver K Λ` of a subfield `Λ ≥ K`,
transported along `fixingSubgroupEquiv`. -/
theorem mem_fixingSubgroup_kOver_iff (Λ : IntermediateField k Ω) (hKΛ : K ≤ Λ)
    (σ : ↥(K.fixingSubgroup)) :
    (IntermediateField.fixingSubgroupEquiv K) σ ∈ (kOver k Ω K Λ hKΛ).fixingSubgroup ↔
      (σ : Ω ≃ₐ[k] Ω) ∈ Λ.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x hx => h x hx, fun h x hx => h x hx⟩

/-- `mapFix` of the fixing subgroup of a subfield `Λ ≥ K` is the fixing subgroup of the base change
`kOver K Λ`.  This is the "finite subextension over `k` ↦ finite subextension over `↥K`" half of
the correspondence of open subgroups. -/
theorem mapFix_fixingSubgroup_kOver (Λ : IntermediateField k Ω) (hKΛ : K ≤ Λ) :
    mapFix k Ω K Λ.fixingSubgroup (IntermediateField.fixingSubgroup_le hKΛ) =
      (kOver k Ω K Λ hKΛ).fixingSubgroup := by
  ext τ
  rw [mapFix, Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hσ
    change (IntermediateField.fixingSubgroupEquiv K) σ ∈ (kOver k Ω K Λ hKΛ).fixingSubgroup
    rwa [mem_fixingSubgroup_kOver_iff k Ω K Λ hKΛ σ]
  · intro hτ
    refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm τ, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, ← mem_fixingSubgroup_kOver_iff k Ω K Λ hKΛ _]
      rw [MulEquiv.apply_symm_apply]
      exact hτ
    · exact (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply τ

/-- Membership in the fixing subgroup of `M.restrictScalars k` transported along
`fixingSubgroupEquiv`. -/
theorem mem_fixingSubgroup_restrictScalars_iff (M : IntermediateField ↥K Ω)
    (σ : ↥(K.fixingSubgroup)) :
    (IntermediateField.fixingSubgroupEquiv K) σ ∈ M.fixingSubgroup ↔
      (σ : Ω ≃ₐ[k] Ω) ∈ (M.restrictScalars k).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact h x ((IntermediateField.mem_restrictScalars k).mpr hx)
  · intro h x hx
    exact h x ((IntermediateField.mem_restrictScalars k).mp hx)

/-- Every `M : IntermediateField ↥K Ω` contains `K`. -/
theorem le_restrictScalars (M : IntermediateField ↥K Ω) : K ≤ M.restrictScalars k := by
  intro x hx
  rw [IntermediateField.mem_restrictScalars]
  have h := M.algebraMap_mem (⟨x, hx⟩ : ↥K)
  rwa [IntermediateField.algebraMap_apply] at h

/-- `mapFix` of the fixing subgroup of `M.restrictScalars k` is the fixing subgroup of `M`.  This
is the "finite subextension over `↥K` ↦ finite subextension over `k`" half of the correspondence
of open subgroups. -/
theorem mapFix_fixingSubgroup_restrictScalars (M : IntermediateField ↥K Ω) :
    mapFix k Ω K (M.restrictScalars k).fixingSubgroup
        (IntermediateField.fixingSubgroup_le (le_restrictScalars k Ω K M)) =
      M.fixingSubgroup := by
  ext τ
  rw [mapFix, Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hσ
    change (IntermediateField.fixingSubgroupEquiv K) σ ∈ M.fixingSubgroup
    rwa [mem_fixingSubgroup_restrictScalars_iff k Ω K M σ]
  · intro hτ
    refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm τ, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, ← mem_fixingSubgroup_restrictScalars_iff k Ω K M _]
      rw [MulEquiv.apply_symm_apply]
      exact hτ
    · exact (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply τ

/-- A subfield `M` of `Ω` finite over `↥K` is finite over `k` (viewed through
`restrictScalars`): this is the tower formula. -/
theorem finiteDimensional_restrictScalars (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] :
    FiniteDimensional k (M.restrictScalars k) :=
  FiniteDimensional.trans k (↥K) M

end Helpers

theorem isLocConstOn_mapFix_iff (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ)
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H ≤ K.fixingSubgroup)
    (f : (Ω ≃ₐ[k] Ω) → ZMod p) (f' : (Ω ≃ₐ[↥K] Ω) → ZMod p)
    (hag : ∀ x : ↥(K.fixingSubgroup), f' (IntermediateField.fixingSubgroupEquiv K x)
      = f (x : Ω ≃ₐ[k] Ω)) :
    SSGRoute.IsLocConstOn H f ↔
      SSGRoute.IsLocConstOn (Work.SSGRoute.ZSplit.mapFix k Ω K H hH) f' := by
  -- Normal form: it suffices to test the constancy on the fixing subgroup of a *finite*
  -- subextension, because the Krull topology is generated by those.
  have hL : SSGRoute.IsLocConstOn H f ↔
      ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧
        ∀ g ∈ H, ∀ u ∈ E.fixingSubgroup, u ∈ H → f (g * u) = f g := by
    rw [SSGRoute.IsLocConstOn]
    constructor
    · rintro ⟨U, hUo, hU⟩
      have hmem : (U : Set (Ω ≃ₐ[k] Ω)) ∈ 𝓝 (1 : Ω ≃ₐ[k] Ω) := hUo.mem_nhds U.one_mem
      rw [krullTopology_mem_nhds_one_iff] at hmem
      obtain ⟨E, hEfin, hEU⟩ := hmem
      exact ⟨E, hEfin, fun g hg u hu huH => hU g hg u (hEU hu) huH⟩
    · rintro ⟨E, hEfin, hE⟩
      exact ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E, hE⟩
  have hR : SSGRoute.IsLocConstOn (Work.SSGRoute.ZSplit.mapFix k Ω K H hH) f' ↔
      ∃ E : IntermediateField ↥K Ω, FiniteDimensional ↥K E ∧
        ∀ g ∈ Work.SSGRoute.ZSplit.mapFix k Ω K H hH, ∀ u ∈ E.fixingSubgroup,
          u ∈ Work.SSGRoute.ZSplit.mapFix k Ω K H hH → f' (g * u) = f' g := by
    rw [SSGRoute.IsLocConstOn]
    constructor
    · rintro ⟨U, hUo, hU⟩
      have hmem : (U : Set (Ω ≃ₐ[↥K] Ω)) ∈ 𝓝 (1 : Ω ≃ₐ[↥K] Ω) := hUo.mem_nhds U.one_mem
      rw [krullTopology_mem_nhds_one_iff] at hmem
      obtain ⟨E, hEfin, hEU⟩ := hmem
      exact ⟨E, hEfin, fun g hg u hu huH => hU g hg u (hEU hu) huH⟩
    · rintro ⟨E, hEfin, hE⟩
      exact ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E, hE⟩
  rw [hL, hR]
  constructor
  · -- over `k` ⟹ over `↥K`
    rintro ⟨E, hEfin, hE⟩
    haveI : FiniteDimensional k (E ⊔ K : IntermediateField k Ω) := inferInstance
    refine ⟨kOver k Ω K (E ⊔ K) le_sup_right,
      finiteDimensional_kOver k Ω K (E ⊔ K) le_sup_right, ?_⟩
    intro g hg u hu huH
    rw [Work.SSGRoute.ZSplit.mapFix, Subgroup.mem_map] at hg huH
    obtain ⟨g₀, hg₀, hg₀eq⟩ := hg
    obtain ⟨u₀, hu₀, hu₀eq⟩ := huH
    rw [Subgroup.mem_subgroupOf] at hg₀ hu₀
    have hu₀E : (u₀ : Ω ≃ₐ[k] Ω) ∈ E.fixingSubgroup := by
      have h1 : (u₀ : Ω ≃ₐ[k] Ω) ∈ (E ⊔ K : IntermediateField k Ω).fixingSubgroup := by
        rw [← mem_fixingSubgroup_kOver_iff k Ω K (E ⊔ K) le_sup_right u₀]
        rw [show (IntermediateField.fixingSubgroupEquiv K) u₀ = u from hu₀eq]
        exact hu
      exact IntermediateField.fixingSubgroup_le le_sup_left h1
    have hmain : f ((g₀ : Ω ≃ₐ[k] Ω) * (u₀ : Ω ≃ₐ[k] Ω)) = f (g₀ : Ω ≃ₐ[k] Ω) :=
      hE _ hg₀ _ hu₀E hu₀
    have hg₀eq' : (IntermediateField.fixingSubgroupEquiv K) g₀ = g := hg₀eq
    have hu₀eq' : (IntermediateField.fixingSubgroupEquiv K) u₀ = u := hu₀eq
    have hstep1 : f' (g * u) = f ((g₀ : Ω ≃ₐ[k] Ω) * (u₀ : Ω ≃ₐ[k] Ω)) := by
      rw [← hg₀eq', ← hu₀eq', ← map_mul]
      exact hag (g₀ * u₀)
    have hstep2 : f' g = f (g₀ : Ω ≃ₐ[k] Ω) := by
      rw [← hg₀eq']
      exact hag g₀
    rw [hstep1, hstep2]
    exact hmain
  · -- over `↥K` ⟹ over `k`
    rintro ⟨E', hE'fin, hE'⟩
    refine ⟨E'.restrictScalars k, finiteDimensional_restrictScalars k Ω K E', ?_⟩
    intro g hg u hu huH
    have hgK : g ∈ K.fixingSubgroup := hH hg
    have huK : u ∈ K.fixingSubgroup := hH huH
    have hmem_g : (IntermediateField.fixingSubgroupEquiv K) ⟨g, hgK⟩
        ∈ Work.SSGRoute.ZSplit.mapFix k Ω K H hH := by
      rw [Work.SSGRoute.ZSplit.mapFix, Subgroup.mem_map]
      exact ⟨⟨g, hgK⟩, hg, rfl⟩
    have hmem_u : (IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩
        ∈ Work.SSGRoute.ZSplit.mapFix k Ω K H hH := by
      rw [Work.SSGRoute.ZSplit.mapFix, Subgroup.mem_map]
      exact ⟨⟨u, huK⟩, huH, rfl⟩
    have hmem_u_fix : (IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩ ∈ E'.fixingSubgroup :=
      (mem_fixingSubgroup_restrictScalars_iff k Ω K E' ⟨u, huK⟩).mpr hu
    have hthis := hE' _ hmem_g _ hmem_u_fix hmem_u
    rw [← map_mul, hag (⟨g, hgK⟩ * ⟨u, huK⟩), hag ⟨g, hgK⟩] at hthis
    exact hthis

end Work.SSGRoute.ZSplit.KTransport

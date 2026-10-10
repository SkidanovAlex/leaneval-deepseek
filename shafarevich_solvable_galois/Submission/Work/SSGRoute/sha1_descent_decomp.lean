import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.chebotarev_descent_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ш¹` at the finite level: the local conditions descend to the decomposition subgroups

Write `G = Gal(K/k)`, so that `G_k = Ω ≃ₐ[k] Ω` maps onto `G` by `res k K`, with kernel `G_K`.  For
`ψ : G → M` a `1`-cocycle, the pullback `ψ ∘ res k K` lies in `Z1loc` as soon as `ψ` is a
coboundary on the image `(decomp k A).map (res k K) ⊆ G` of every decomposition group and on the
image of every involution — and *conversely* the descent `descentZ1 z` of any `z ∈ Z1loc` satisfies
exactly these conditions.  The second direction is cheap because the local condition of
`Submission/Work/SSGRoute/Interfaces.lean` is the *strong* one: a coboundary on `H ≤ G_k` is
`z g = res g • m - m` for a **single** `m ∈ M`; since `G_K` acts trivially on `M`, that same `m` is
a primitive for the restriction of the descended cocycle to the image of `H`.

Consequently (`sha1DescentHom` is injective, `Submission/Work/SSGRoute/sha1_descent_H1.lean`)

  `Ш¹(k,M) ≅ { ψ̄ ∈ H¹(Gal(K/k), M) : ψ̄ vanishes on (decomp k A).map (res k K) for every finite
                                      place A, and likewise on the image of every involution }`.

This is node `E1b` of `Submission/Work/SSGRoute/DESIGN_EXT.md` (there phrased through
`Ext¹_G(E', Kˣ)`); it is the "Hasse principle" half of the Poitou–Tate package, and the input that
converts the Tate duality `Ĥ⁻²(G, M ⊗ T) ≅ H¹(G, M^∨(1))^∨` into information about `Ш²`.
-/

set_option linter.ambiguousOpen false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open SSGRoute




/-- `res k K` is trivial on the fixing subgroup of `K`. -/
theorem res_eq_one_of_mem_fixingSubgroup {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    SSGRoute.res k K σ = 1 := by
  ext x
  rw [AlgEquiv.restrictNormalHom_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff K σ).mp hσ x x.2

/-- **The local conditions of `Z1loc` descend to `G = Gal(K/k)`.**  If `z = ψ ∘ res k K` is a
coboundary on the decomposition group of the finite place `A`, then `ψ` is a coboundary on the
image `(decomp k A).map (res k K)`: the primitive `m` of `z` on `decomp k A` is a primitive for `ψ`
on the image, because `G_K` acts trivially on `M`. -/
theorem isCoboundaryOn_map_of_descent {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] {M : Type} [AddCommGroup M]
    [DistribMulAction (K ≃ₐ[k] K) M] {ψ : (K ≃ₐ[k] K) → M} {z : (Ω ≃ₐ[k] Ω) → M}
    (h : z = ψ ∘ SSGRoute.res k K)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) z) :
    ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        ((SSGRoute.decomp k A).map (SSGRoute.res k K)) ψ := by
  intro A hA
  obtain ⟨m, hm⟩ := hloc A hA
  refine ⟨m, fun τ hτ => ?_⟩
  obtain ⟨σ, hσ, rfl⟩ := hτ
  have h1 : z σ = ψ (SSGRoute.res k K σ) := congrFun h σ
  rw [← h1]
  exact hm σ hσ

/-- **The local conditions at the images of the involutions descend** (archimedean places). -/
theorem isCoboundaryOn_map_zpowers_of_descent {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] {M : Type} [AddCommGroup M]
    [DistribMulAction (K ≃ₐ[k] K) M] {ψ : (K ≃ₐ[k] K) → M} {z : (Ω ≃ₐ[k] Ω) → M}
    (h : z = ψ ∘ SSGRoute.res k K)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers σ) z) :
    ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        ((Subgroup.zpowers σ).map (SSGRoute.res k K)) ψ := by
  intro σ hσ
  obtain ⟨m, hm⟩ := hinf σ hσ
  refine ⟨m, fun τ hτ => ?_⟩
  obtain ⟨ρ, hρ, rfl⟩ := hτ
  have h1 : z ρ = ψ (SSGRoute.res k K ρ) := congrFun h ρ
  rw [← h1]
  exact hm ρ hρ

section Sha1Descent

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)]

variable {M : Type} [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]

/-- **Converse of the descent of the local conditions**: a `G`-cocycle which is a coboundary on the
image of every decomposition group and of every involution pulls back to an element of `Z1loc`. -/
theorem mem_Z1loc_of_map_coboundary (ψ : (K ≃ₐ[k] K) → M)
    (hψ : SSGRoute.IsCocycleOn (MonoidHom.id (K ≃ₐ[k] K)) ⊤ ψ)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        ((SSGRoute.decomp k A).map (SSGRoute.res k K)) ψ)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        ((Subgroup.zpowers σ).map (SSGRoute.res k K)) ψ) :
    (fun σ => ψ (SSGRoute.res k K σ)) ∈ Z1loc p k Ω K M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g _ h _
    show ψ (SSGRoute.res k K (g * h)) = ψ (SSGRoute.res k K g)
      + SSGRoute.res k K g • ψ (SSGRoute.res k K h)
    rw [map_mul]
    exact hψ (SSGRoute.res k K g) trivial (SSGRoute.res k K h) trivial
  · refine ⟨K.fixingSubgroup, K.fixingSubgroup_isOpen, fun g _ u hu _ => ?_⟩
    have hu1 : SSGRoute.res k K u = 1 := res_eq_one_of_mem_fixingSubgroup hu
    show ψ (SSGRoute.res k K (g * u)) = ψ (SSGRoute.res k K g)
    rw [map_mul, hu1, mul_one]
  · intro A hA
    obtain ⟨m, hm⟩ := hloc A hA
    exact ⟨m, fun g hg => hm (SSGRoute.res k K g) (Subgroup.mem_map_of_mem _ hg)⟩
  · intro σ hσ
    obtain ⟨m, hm⟩ := hinf σ hσ
    exact ⟨m, fun g hg => hm (SSGRoute.res k K g) (Subgroup.mem_map_of_mem _ hg)⟩

/-- **The descended cocycle of `z ∈ Z1loc` satisfies the finite-level local conditions.** -/
theorem isCoboundaryOn_map_descentZ1 (z : ↥(Z1loc p k Ω K M)) :
    (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
        SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
          ((SSGRoute.decomp k A).map (SSGRoute.res k K)) (descentZ1 p k Ω K M z).1) ∧
      (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
        SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
          ((Subgroup.zpowers σ).map (SSGRoute.res k K)) (descentZ1 p k Ω K M z).1) := by
  obtain ⟨_, _, hloc, hinf⟩ := z.2
  exact ⟨isCoboundaryOn_map_of_descent (K := K) (descentZ1_comp_res p k Ω K M z) hloc,
    isCoboundaryOn_map_zpowers_of_descent (K := K) (descentZ1_comp_res p k Ω K M z) hinf⟩

/-- **Description of the range of the Hasse descent.**  A cocycle `ψ` on `G = Gal(K/k)` is the
descent of an element of `Z1loc` — equivalently, its class lies in the image of
`sha1DescentHom : Ш¹(k,M) ↪ H¹(G,M)` — if and only if it is a coboundary on the image of every
decomposition group and of every involution. -/
theorem exists_descent_iff (ψ : (K ≃ₐ[k] K) → M)
    (hψ : SSGRoute.IsCocycleOn (MonoidHom.id (K ≃ₐ[k] K)) ⊤ ψ) :
    (∃ z : ↥(Z1loc p k Ω K M), (descentZ1 p k Ω K M z).1 = ψ) ↔
      (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
        SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
          ((SSGRoute.decomp k A).map (SSGRoute.res k K)) ψ) ∧
      (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
        SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
          ((Subgroup.zpowers σ).map (SSGRoute.res k K)) ψ) := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨_, _, hloc, hinf⟩ := z.2
    have hcomp : z.1 = ψ ∘ SSGRoute.res k K := by
      rw [descentZ1_comp_res p k Ω K M z, hz]
    exact ⟨isCoboundaryOn_map_of_descent (K := K) hcomp hloc,
      isCoboundaryOn_map_zpowers_of_descent (K := K) hcomp hinf⟩
  · intro h
    have hmem : (fun σ => ψ (SSGRoute.res k K σ)) ∈ Z1loc p k Ω K M :=
      mem_Z1loc_of_map_coboundary p k Ω K ψ hψ h.1 h.2
    refine ⟨⟨fun σ => ψ (SSGRoute.res k K σ), hmem⟩, ?_⟩
    exact descentZ1_val_eq_of p k Ω K M ⟨fun σ => ψ (SSGRoute.res k K σ), hmem⟩ rfl

end Sha1Descent

end Work.SSGRoute

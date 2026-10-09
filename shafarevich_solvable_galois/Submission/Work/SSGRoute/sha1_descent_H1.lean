import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.chebotarev_descent_defs
import Submission.Work.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Hasse descent `Ш¹(k,M) ↪ H¹(Gal(K/k), M)`: injective and natural

For a number field `k`, an algebraic closure `Ω`, a finite Galois extension `K/k` inside `Ω` and a
finite `𝔽_p[Gal(K/k)]`-module `M`, every locally trivial continuous `1`-cocycle descends to
`Gal(K/k)` (Chebotarev/Bauer, `Work.SSGRoute.hassePrinciple_h1_cocycles`), and the descent is
*unique* since `G_k → Gal(K/k)` is surjective (`Submission/Work/SSGRoute/chebotarev_descent_defs`).
Hence `descentHom` kills the global coboundaries and induces the map

  `Work.SSGRoute.sha1Descent p k Ω K M : Ш¹(k,M) →+ H¹(Gal(K/k), M)`,

proved here to be **injective** and **natural** in `M`.

Why this is the right form: by Tate–Poitou duality `Ш²(k,E) ≅ Ш¹(k, E^∨(1))^∨`, so a *surjection*
`Ĥ⁻²(Gal(K/k), E ⊗ μ_p^∨) ↠ Ш²(k,E)` — the Claim of Schmidt–Wingberg, §5 Step 2, = Milne,
*Arithmetic Duality Theorems*, I.4.10, and the content of `Work.SSGRoute.tatePoitou_sha2_image` — is
the *dual* of the **injectivity** of the present descent map at the dual coefficient module
`E^∨(1) = Hom(E, μ_p)`.  This is exactly the "Hasse principle" step of the proof of that Claim.
-/

set_option linter.ambiguousOpen false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute

open SSGRoute

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)]

/-- **The descent kills the global coboundaries.** If `z ∈ Z¹_loc` is the coboundary of `m`, then
`z` descends to the coboundary `τ ↦ τ • m - m`, whose class in `H¹(Gal(K/k), M)` is zero. -/
theorem descentHom_eq_zero_of_mem_B1top
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) (hz : (z : (Ω ≃ₐ[k] Ω) → M) ∈ B1top p k Ω K M) :
    descentHom p k Ω K M z = 0 := by
  have hz1 : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ (z : (Ω ≃ₐ[k] Ω) → M) := hz
  obtain ⟨m, hm⟩ := hz1
  have hψ1 : SSGRoute.IsCocycleOn (MonoidHom.id (K ≃ₐ[k] K)) ⊤
      (fun τ : K ≃ₐ[k] K => τ • m - m) := by
    intro τ _ τ' _
    show (τ * τ') • m - m = (τ • m - m) + τ • (τ' • m - m)
    simp only [mul_smul, smul_sub]
    abel
  have hcomp : (z : (Ω ≃ₐ[k] Ω) → M)
      = (fun τ : K ≃ₐ[k] K => τ • m - m) ∘ SSGRoute.res k K := by
    funext σ
    exact hm σ trivial
  have hdes : descentZ1 p k Ω K M z
      = ⟨fun τ : K ≃ₐ[k] K => τ • m - m,
          (isCocycleOn_iff_mem_Z1 (MonoidHom.id (K ≃ₐ[k] K)) _).mp hψ1⟩ :=
    descentZ1_eq_of p k Ω K M z _ hcomp
  rw [descentHom_apply, hdes, Work.GroupCohomology.H1pi_eq_zero_iff,
    Work.GroupCohomology.mem_B1_iff]
  refine ⟨m, ?_⟩
  funext τ
  rw [Work.GroupCohomology.d0_apply]

/-- **The Hasse descent detects `Ш¹`**: if the descended class of `z ∈ Z¹_loc` is zero in
`H¹(Gal(K/k), M)`, then `z` is a global coboundary, i.e. its class in `Ш¹(k,M)` is zero.  This is
the injectivity of the induced map `Ш¹(k,M) →+ H¹(Gal(K/k), M)` on representatives. -/
theorem descentHom_eq_zero_iff_mem_B1top
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) :
    descentHom p k Ω K M z = 0 ↔ (z : (Ω ≃ₐ[k] Ω) → M) ∈ B1top p k Ω K M := by
  refine ⟨?_, descentHom_eq_zero_of_mem_B1top p k Ω K M z⟩
  intro hz
  have h1 : Work.GroupCohomology.H1π (K ≃ₐ[k] K) M (descentZ1 p k Ω K M z) = 0 := by
    rw [← descentHom_apply p k Ω K M z]; exact hz
  obtain ⟨m, hm⟩ := (Work.GroupCohomology.mem_B1_iff (K ≃ₐ[k] K) M _).mp
    ((Work.GroupCohomology.H1pi_eq_zero_iff (descentZ1 p k Ω K M z)).mp h1)
  refine ⟨m, fun g _ => ?_⟩
  have h2 : (z : (Ω ≃ₐ[k] Ω) → M) g = (descentZ1 p k Ω K M z).1 (SSGRoute.res k K g) :=
    congrFun (descentZ1_comp_res p k Ω K M z) g
  rw [h2, ← hm, Work.GroupCohomology.d0_apply]

/-- **Naturality of the Hasse descent** in the coefficient module, on the level of the cocycles
`Z¹_loc`: the descent of the push-forward of `z` along a `Gal(K/k)`-equivariant `𝔽_p`-linear map
`f : M → N` is the push-forward of the descent of `z`. -/
theorem descentHom_pushC1
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N] [Finite N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    (z : ↥(Z1loc p k Ω K M)) :
    descentHom p k Ω K N ⟨(pushC1 p k Ω K M N f) (z : (Ω ≃ₐ[k] Ω) → M),
        Z1loc_pushC1_mem p k Ω K M N f hf (z : (Ω ≃ₐ[k] Ω) → M) z.2⟩
      = Work.GroupCohomology.mapH1 (K ≃ₐ[k] K) f.toAddMonoidHom hf (descentHom p k Ω K M z) := by
  have hfun : (⟨(pushC1 p k Ω K M N f) (z : (Ω ≃ₐ[k] Ω) → M),
        Z1loc_pushC1_mem p k Ω K M N f hf (z : (Ω ≃ₐ[k] Ω) → M) z.2⟩ :
          ↥(Z1loc p k Ω K N)).1
      = (Work.GroupCohomology.mapZ1 (K ≃ₐ[k] K) f.toAddMonoidHom hf
          (descentZ1 p k Ω K M z)).1 ∘ SSGRoute.res k K := by
    funext σ
    have h1 : (descentZ1 p k Ω K M z).1 (SSGRoute.res k K σ)
        = (z : (Ω ≃ₐ[k] Ω) → M) σ :=
      (congrFun (descentZ1_comp_res p k Ω K M z) σ).symm
    show f ((z : (Ω ≃ₐ[k] Ω) → M) σ)
      = Work.GroupCohomology.mapCochain1 (K ≃ₐ[k] K) f.toAddMonoidHom
          ((descentZ1 p k Ω K M z).1) (SSGRoute.res k K σ)
    rw [Work.GroupCohomology.mapCochain1_apply]
    exact congrArg f h1.symm
  have hdes : descentZ1 p k Ω K N
      ⟨(pushC1 p k Ω K M N f) (z : (Ω ≃ₐ[k] Ω) → M),
        Z1loc_pushC1_mem p k Ω K M N f hf (z : (Ω ≃ₐ[k] Ω) → M) z.2⟩
      = Work.GroupCohomology.mapZ1 (K ≃ₐ[k] K) f.toAddMonoidHom hf
          (descentZ1 p k Ω K M z) :=
    descentZ1_eq_of p k Ω K N _ _ hfun
  rw [descentHom_apply, descentHom_apply, hdes]
  exact Work.GroupCohomology.mapH1_H1π (K ≃ₐ[k] K) f.toAddMonoidHom hf (descentZ1 p k Ω K M z)

/-- **The Hasse descent on `Ш¹`.**  The map induced by `descentHom` on the quotient
`Ш¹(k,M) = Z¹_loc/B¹`, obtained from `descentHom_eq_zero_of_mem_B1top` by the universal property of
the quotient. -/
noncomputable def sha1DescentHom
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    Sha1 p k Ω K M →+ Work.GroupCohomology.H1 (K ≃ₐ[k] K) M :=
  QuotientAddGroup.lift
    (Submodule.comap (Z1loc p k Ω K M).subtype (B1top p k Ω K M)).toAddSubgroup
    (descentHom p k Ω K M)
    (fun z hz => descentHom_eq_zero_of_mem_B1top p k Ω K M z (Submodule.mem_comap.mp hz))

/-- The value of `sha1DescentHom` on the class of a cocycle. -/
theorem sha1DescentHom_mk
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) :
    sha1DescentHom p k Ω K M (Submodule.Quotient.mk z) = descentHom p k Ω K M z :=
  QuotientAddGroup.lift_mk' _ _ z

/-- **`Ш¹(k,M) ↪ H¹(Gal(K/k), M)`**: the Hasse descent is injective on `Ш¹`. -/
theorem sha1DescentHom_injective
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    Function.Injective (sha1DescentHom p k Ω K M) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := (B1top p k Ω K M).comap (Z1loc p k Ω K M).subtype) x
  have hx' : descentHom p k Ω K M z = 0 := by
    rw [← sha1DescentHom_mk p k Ω K M z]; exact hx
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact (descentHom_eq_zero_iff_mem_B1top p k Ω K M z).mp hx'

/-- **Naturality of the Hasse descent** w.r.t. a `Gal(K/k)`-equivariant `𝔽_p`-linear map. -/
theorem sha1DescentHom_natural
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N] [Finite N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    (x : Sha1 p k Ω K M) :
    sha1DescentHom p k Ω K N (Sha1Map p k Ω K M N f hf x) =
      Work.GroupCohomology.mapH1 (K ≃ₐ[k] K) f.toAddMonoidHom hf
        (sha1DescentHom p k Ω K M x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := (B1top p k Ω K M).comap (Z1loc p k Ω K M).subtype) x
  rw [Sha1Map_mk, sha1DescentHom_mk, sha1DescentHom_mk, descentHom_pushC1]

end Work.SSGRoute

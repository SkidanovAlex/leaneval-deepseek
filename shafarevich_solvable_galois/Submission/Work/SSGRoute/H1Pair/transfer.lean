import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.SSGRoute.H1Pair.Natural
import Submission.Work.SSGRoute.H1Pair.obstruction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

open SSGRoute
open scoped TensorProduct
open CategoryTheory

namespace Work.SSGRoute.H1Pair

/-- **The contragredient action is the `DualMod` action through `π`**: on the contragredient of a
restricted representation, `σ` acts by the dual action of `π σ`
(`Work.SSGRoute.DualMod.dualSMul`), i.e. `ψ ↦ ψ ∘ ((π σ)⁻¹ • ·)`. -/
theorem contra_res_ρ_apply (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K N : IntermediateField k Ω) [Normal k N]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (π : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K)) (σ : N ≃ₐ[k] N) (m : Work.SSGRoute.DualMod p M) :
    (contra (Rep.res π (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) M)))).ρ σ m
      = (π σ) • m := by
  rw [show (contra (Rep.res π (Rep.of (Representation.ofDistribMulAction (ZMod p)
        (K ≃ₐ[k] K) M)))).ρ σ
      = ((Rep.res π (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) M))).ρ.dual) σ
    from rfl, Representation.dual_apply, Module.Dual.transpose_apply]
  ext x
  rw [LinearMap.comp_apply,
    DFunLike.congr_fun (Rep.res_obj_ρ π
      (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) M))) σ⁻¹,
    MonoidHom.comp_apply, Representation.ofDistribMulAction_apply_apply]
  simp only [Work.SSGRoute.DualMod.dualSMul_apply, map_inv]

/-- **Mathlib's cocycles of the contragredient are the `IsCocycleOn`-cocycles of the restriction**:
a `1`-cocycle on `Gal(N/k)` with values in `M^∨(1)` satisfies the crossed-homomorphism condition
with respect to the action of `G_k` through `res k K`, after composing with `res k N`. -/
theorem isCocycleOn_comp_res_of_mem_cocycles₁_contra (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [Field Ω] [Algebra k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Normal k N]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (π : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπ : ∀ σ : Ω ≃ₐ[k] Ω, π (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (b : (N ≃ₐ[k] N) → Work.SSGRoute.DualMod p M)
    (hb : b ∈ groupCohomology.cocycles₁ (contra (Rep.res π (Rep.of
      (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) M)))))
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) H
      (fun σ => b (SSGRoute.res k N σ)) := by
  intro σ _ τ _
  show b (SSGRoute.res k N (σ * τ))
    = b (SSGRoute.res k N σ) + (SSGRoute.res k K σ) • b (SSGRoute.res k N τ)
  rw [map_mul]
  have h1 := (groupCohomology.mem_cocycles₁_iff
    (A := contra (Rep.res π (Rep.of (Representation.ofDistribMulAction (ZMod p)
      (K ≃ₐ[k] K) M)))) b).1 hb (SSGRoute.res k N σ) (SSGRoute.res k N τ)
  rw [contra_res_ρ_apply p k Ω K N M π (SSGRoute.res k N σ) (b (SSGRoute.res k N τ)), hπ σ] at h1
  rw [h1, add_comm]

/-- **Step 3–4 of the assembly** (the transfer): if the obstruction class `X` of the level-`N` data
dies at the level `N₂` with finite coefficients `M₂` (hypothesis `hF₀zero`), then the level-`N₂`
functional — the data `(f₀ ∘ α, f₀ ∘ β)` paired with `M₂` — **vanishes on every `1`-cocycle** of
`Gal(N₂/k)` with values in `M₂^∨(1)`.

This is the hypothesis `horth` of Poitou–Tate (`Work.SSGRoute.pt_selmer_relaxed`), in the exact form
in which the assembly consumes it.  The whole content is the representative identity for
`groupCohomology.map` (Mathlib) plus the **naturality of the local pairings in the coefficient
module** (`hnat`, clause (4)), applied at every group of `S` and `C`. -/
theorem transfer_sum_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K N N₂ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [FiniteDimensional k N₂] [IsGalois k N₂]
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπN : ∀ σ : Ω ≃ₐ[k] Ω, πN (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (q : (N ≃ₐ[k] N) →* (N₂ ≃ₐ[k] N₂))
    (hq : ∀ σ : Ω ≃ₐ[k] Ω, q (SSGRoute.res k N σ) = SSGRoute.res k N₂ σ)
    (π₂ : (N₂ ≃ₐ[k] N₂) →* (K ≃ₐ[k] K))
    (hπ₂ : ∀ σ : Ω ≃ₐ[k] Ω, π₂ (SSGRoute.res k N₂ σ) = SSGRoute.res k K σ)
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f₀ : E →ₗ[ZMod p] M₂) (hf₀ : ∀ (g : K ≃ₐ[k] K) (e : E), f₀ (g • e) = g • f₀ e)
    (pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
          ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p)
    (hnat : ∀ (M M' : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction (K ≃ₐ[k] K) M']
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M'] [Finite M']
        (f : M →ₗ[ZMod p] M') (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
        (f' : Work.SSGRoute.DualMod p (M' ⊗[ZMod p] T) →ₗ[ZMod p]
          Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (hff' : ∀ (φ : Work.SSGRoute.DualMod p (M' ⊗[ZMod p] T)) (e : M) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M' ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        pair M' H (fun σ => f (a σ)) b = pair M H a (fun σ => f' (b σ)))
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → E)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (X : groupHomology.H1 (Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p)
          (K ≃ₐ[k] K) (TensorProduct (ZMod p) E T)))))
    (Φ : ↥(groupCohomology.cocycles₁ (contra (Rep.res πN (Rep.of
          (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
            (TensorProduct (ZMod p) E T)))))) →ₗ[ZMod p] ZMod p)
    (hΦ : ∀ b : ↥(groupCohomology.cocycles₁ (contra (Rep.res πN (Rep.of
          (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
            (TensorProduct (ZMod p) E T)))))),
        Φ b = S.sum (fun A => pair E (SSGRoute.decomp k A) (α A)
            (fun σ => b.1 (SSGRoute.res k N σ))) +
          C.sum (fun c => pair E (Subgroup.zpowers c) (β c)
            (fun σ => b.1 (SSGRoute.res k N σ))))
    (hX : ∀ b : ↥(groupCohomology.cocycles₁ (contra (Rep.res πN (Rep.of
          (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
            (TensorProduct (ZMod p) E T)))))),
        tatePairLin (Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p)
            (K ≃ₐ[k] K) (TensorProduct (ZMod p) E T)))) X
          ((groupCohomology.H1π (contra (Rep.res πN (Rep.of
            (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
              (TensorProduct (ZMod p) E T)))))).hom b) = Φ b)
    (F₀ : Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
            (TensorProduct (ZMod p) E T))) ⟶
          Rep.res q (Rep.res π₂ (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
            (TensorProduct (ZMod p) M₂ T)))))
    (hF₀tmul : ∀ (e : E) (t : T), F₀.hom (e ⊗ₜ[ZMod p] t) = f₀ e ⊗ₜ[ZMod p] t)
    (hF₀zero : (groupHomology.map q F₀ 1).hom X = 0) :
    ∀ (b₀ : (N₂ ≃ₐ[k] N₂) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T))
      (hb₀ : b₀ ∈ groupCohomology.cocycles₁ (contra (Rep.res π₂ (Rep.of
        (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
          (TensorProduct (ZMod p) M₂ T)))))),
      S.sum (fun A => pair M₂ (SSGRoute.decomp k A) (fun σ => f₀ (α A σ))
          (fun τ => b₀ (SSGRoute.res k N₂ τ))) +
        C.sum (fun c => pair M₂ (Subgroup.zpowers c) (fun σ => f₀ (β c σ))
          (fun τ => b₀ (SSGRoute.res k N₂ τ))) = 0 := by
  classical
  intro b₀ hb₀
  -- names for the four coefficient representations
  let AN : Rep (ZMod p) (N ≃ₐ[k] N) := Rep.res πN (Rep.of (Representation.ofDistribMulAction
    (ZMod p) (K ≃ₐ[k] K) (TensorProduct (ZMod p) E T)))
  let BN : Rep (ZMod p) (N₂ ≃ₐ[k] N₂) := Rep.res π₂ (Rep.of (Representation.ofDistribMulAction
    (ZMod p) (K ≃ₐ[k] K) (TensorProduct (ZMod p) M₂ T)))
  let F₀' : Rep.res q (contra BN) ⟶ contra AN := repTranspose F₀
  -- the cochain representative of `(map q F₀' 1) [b₀]`
  let θ : ↥(groupCohomology.cocycles₁ (contra AN)) :=
    groupCohomology.mapCocycles₁ q F₀' ⟨b₀, hb₀⟩
  have hθ : ∀ σ : N ≃ₐ[k] N, θ.1 σ = F₀'.hom (b₀ (q σ)) := by
    intro σ
    show (groupCohomology.cochainsMap₁ q F₀' b₀) σ = F₀'.hom (b₀ (q σ))
    exact congrFun (cochainsMap₁_apply q F₀' b₀) σ
  have hmap : (groupCohomology.map q F₀' 1).hom ((groupCohomology.H1π (contra BN)).hom
      ⟨b₀, hb₀⟩) = (groupCohomology.H1π (contra AN)).hom θ :=
    groupCohomology.H1π_comp_map_apply (A := contra BN) (B := contra AN) (f := q) F₀' ⟨b₀, hb₀⟩
  have hF'transpose : ∀ (ψ : (contra BN).V) (v : AN.V), F₀'.hom ψ v = ψ (F₀.hom v) :=
    fun ψ v => repTranspose_hom_apply F₀ ψ v
  have hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : E) (t : T),
      F₀'.hom φ (e ⊗ₜ[ZMod p] t) = φ (f₀ e ⊗ₜ[ZMod p] t) := by
    intro φ e t
    rw [hF'transpose φ (e ⊗ₜ[ZMod p] t), hF₀tmul e t]
  -- the two sums are the same, by naturality of the pairings in the coefficient module
  have hstep : S.sum (fun A => pair M₂ (SSGRoute.decomp k A) (fun σ => f₀ (α A σ))
        (fun τ => b₀ (SSGRoute.res k N₂ τ))) =
      S.sum (fun A => pair E (SSGRoute.decomp k A) (α A)
        (fun σ => F₀'.hom (b₀ (SSGRoute.res k N₂ σ)))) := by
    refine Finset.sum_congr rfl fun A hA => ?_
    exact hnat E M₂ f₀ hf₀ F₀'.hom hff' (SSGRoute.decomp k A) (α A)
      (fun τ => b₀ (SSGRoute.res k N₂ τ)) (hα A hA)
      ⟨isCocycleOn_comp_res_of_mem_cocycles₁_contra p k Ω K N₂ (TensorProduct (ZMod p) M₂ T) π₂ hπ₂ b₀ hb₀
          (SSGRoute.decomp k A),
        isLocConstOn_comp_res N₂ b₀ (SSGRoute.decomp k A)⟩
  have hstepC : C.sum (fun c => pair M₂ (Subgroup.zpowers c) (fun σ => f₀ (β c σ))
        (fun τ => b₀ (SSGRoute.res k N₂ τ))) =
      C.sum (fun c => pair E (Subgroup.zpowers c) (β c)
        (fun σ => F₀'.hom (b₀ (SSGRoute.res k N₂ σ)))) := by
    refine Finset.sum_congr rfl fun c hc => ?_
    exact hnat E M₂ f₀ hf₀ F₀'.hom hff' (Subgroup.zpowers c) (β c)
      (fun τ => b₀ (SSGRoute.res k N₂ τ)) ⟨hβ c hc, isLocConstOn_zpowers_of_sq_eq_one c
        (hCinv c hc) (β c)⟩
      ⟨isCocycleOn_comp_res_of_mem_cocycles₁_contra p k Ω K N₂ (TensorProduct (ZMod p) M₂ T) π₂ hπ₂ b₀ hb₀
          (Subgroup.zpowers c),
        isLocConstOn_comp_res N₂ b₀ (Subgroup.zpowers c)⟩
  -- and the level-`N` sum is `Φ θ`
  have hΦθ : Φ θ = S.sum (fun A => pair E (SSGRoute.decomp k A) (α A)
        (fun σ => F₀'.hom (b₀ (SSGRoute.res k N₂ σ)))) +
      C.sum (fun c => pair E (Subgroup.zpowers c) (β c)
        (fun σ => F₀'.hom (b₀ (SSGRoute.res k N₂ σ)))) := by
    rw [hΦ θ]
    congr 1
    · refine Finset.sum_congr rfl fun A hA => ?_
      congr 1
      funext σ
      rw [hθ (SSGRoute.res k N σ), hq σ]
    · refine Finset.sum_congr rfl fun c hc => ?_
      congr 1
      funext σ
      rw [hθ (SSGRoute.res k N σ), hq σ]
  -- the pairing of `X` with `(map q F₀' 1) [b₀]` is `Φ θ`, and it is zero
  have hzero : Φ θ = 0 := by
    rw [← hX θ, ← hmap]
    rw [← tatePairLin_natural q AN BN F₀ F₀' hF'transpose X
      ((groupCohomology.H1π (contra BN)).hom ⟨b₀, hb₀⟩), hF₀zero]
    simp
  rw [hstep, hstepC, ← hΦθ]
  exact hzero

end Work.SSGRoute.H1Pair

/-
# Poitou–Tate orthogonality: from the level-`N₂` vanishing to the `horth` of `pt_selmer_relaxed`

Step 6 of the assembly of `Work.SSGRoute.coker_obstruction`.  `H1Pair.transfer_sum_eq_zero` proves
that the level-`N₂` functional vanishes on every `1`-cocycle of `Gal(N₂/k)` with values in
`M₂^∨(1)`.  The arithmetic input `Work.SSGRoute.selmer_dual_inflated` (Bauer/Chebotarev for the dual
Selmer group) writes every global cocycle `b` satisfying the *Selmer* conditions of level `N₂` as
`b = b₀ ∘ res k N₂` with `b₀` a `1`-cocycle of `Gal(N₂/k)`.  Hence the local pairing sum of `b` is
the level-`N₂` functional evaluated at `[b₀]`, i.e. zero — which is exactly the `horth` hypothesis of
`Work.SSGRoute.pt_selmer_relaxed`.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.selmer_dual_inflated
import Submission.Work.SSGRoute.H1Pair.Pairing
import Submission.Work.SSGRoute.H1Pair.transfer
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

/-- **The converse bridge**: a crossed-homomorphism condition of `G_k` (through `res k K`) on
`b₀ ∘ res k N` is a Mathlib `1`-cocycle of the contragredient representation.  Uses the surjectivity
of the restriction `G_k ↠ Gal(N/k)`. -/
theorem mem_cocycles₁_contra_of_isCocycleOn (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (π : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπ : ∀ σ : Ω ≃ₐ[k] Ω, π (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (b : (N ≃ₐ[k] N) → Work.SSGRoute.DualMod p M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ (fun σ => b (SSGRoute.res k N σ))) :
    b ∈ groupCohomology.cocycles₁ (contra (Rep.res π (Rep.of
      (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) M)))) := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro g h
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (E := Ω) (K₁ := ↥N) g
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (E := Ω) (K₁ := ↥N) h
  rw [← hσ, ← hτ]
  have h1 := hb σ trivial τ trivial
  simp only at h1
  rw [map_mul] at h1
  rw [h1, contra_res_ρ_apply p k Ω K N M π (SSGRoute.res k N σ) (b (SSGRoute.res k N τ)),
    hπ σ, add_comm]

/-- **Step 6 of the assembly**: the `horth` hypothesis of Poitou–Tate.  Given that the level-`N₂`
functional vanishes on every level-`N₂` `1`-cocycle (the conclusion of
`H1Pair.transfer_sum_eq_zero`), every globally defined locally constant cocycle `b` which is a
coboundary on the decomposition groups of the places split in `N₂` (off `S`) and vanishes on the
inertia of the other places (off `S`) has vanishing local pairing sum. -/
theorem horth_of_level_vanishing
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K N₂ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N₂] [IsGalois k N₂] (hKN₂ : K ≤ N₂)
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (π₂ : (N₂ ≃ₐ[k] N₂) →* (K ≃ₐ[k] K))
    (hπ₂ : ∀ σ : Ω ≃ₐ[k] Ω, π₂ (SSGRoute.res k N₂ σ) = SSGRoute.res k K σ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (f₀ : E →ₗ[ZMod p] M₂) (hf₀ : ∀ (g : K ≃ₐ[k] K) (e : E), f₀ (g • e) = g • f₀ e)
    (pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
          ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → E)
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (htransfer : ∀ (b₀ : (N₂ ≃ₐ[k] N₂) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
      b₀ ∈ groupCohomology.cocycles₁ (contra (Rep.res π₂ (Rep.of
        (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
          (TensorProduct (ZMod p) M₂ T))))) →
      S.sum (fun A => pair M₂ (SSGRoute.decomp k A) (fun σ => f₀ (α A σ))
          (fun τ => b₀ (SSGRoute.res k N₂ τ))) +
        C.sum (fun c => pair M₂ (Subgroup.zpowers c) (fun σ => f₀ (β c σ))
          (fun τ => b₀ (SSGRoute.res k N₂ τ))) = 0) :
    ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N₂ B →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N₂ B →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
      S.sum (fun A => pair M₂ (SSGRoute.decomp k A) (fun σ => f₀ (α A σ)) b) +
        C.sum (fun c => pair M₂ (Subgroup.zpowers c) (fun σ => f₀ (β c σ)) b) = 0 := by
  intro b hb hlc hsplit _
  obtain ⟨b₀, hb₀eq⟩ := Work.SSGRoute.selmer_dual_inflated (k := k) (Ω := Ω) K N₂ hKN₂
    (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) S b hb hlc hsplit
  have hb₀coc : b₀ ∈ groupCohomology.cocycles₁ (contra (Rep.res π₂ (Rep.of
      (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
        (TensorProduct (ZMod p) M₂ T))))) := by
    refine mem_cocycles₁_contra_of_isCocycleOn p k Ω K N₂ (TensorProduct (ZMod p) M₂ T) π₂ hπ₂
      b₀ ?_
    intro σ _ τ _
    show b₀ (SSGRoute.res k N₂ (σ * τ))
      = b₀ (SSGRoute.res k N₂ σ) + (SSGRoute.res k K σ) • b₀ (SSGRoute.res k N₂ τ)
    rw [← hb₀eq (σ * τ), ← hb₀eq σ, ← hb₀eq τ]
    exact hb σ trivial τ trivial
  have h0 := htransfer b₀ hb₀coc
  have hfun : (fun τ : Ω ≃ₐ[k] Ω => b₀ (SSGRoute.res k N₂ τ)) = b := funext fun τ => (hb₀eq τ).symm
  rw [hfun] at h0
  exact h0

end Work.SSGRoute.H1Pair

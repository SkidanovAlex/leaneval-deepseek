import Mathlib
import Submission.Work.SSGRoute.PT.pt_unramifiedSub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped Pointwise

/-- **Conjugation identity for the values of a `1`-cocycle.**

If `x` is a (crossed-homomorphism) `1`-cocycle for `act : Γ →* G` and `act σ = 1`, then the value
of `x` at `σ` can be moved across a conjugating element `g`:

`x σ = act g • x (g⁻¹ * σ * g)`.

This is the algebraic input of the transfer of inertia-vanishing conditions to conjugate places: for
`τ` in the inertia group of a place unramified in the base field, `act τ = 1`, and conjugate
inertia elements are inertia elements by `Work.SSGRoute.isInertia_conj`. -/
theorem cocycle_conj_eq {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] {act : Γ →* G} {x : Γ → M}
    (hx : SSGRoute.IsCocycleOn act ⊤ x) {σ : Γ} (hσ : act σ = 1) (g : Γ) :
    x σ = act g • x (g⁻¹ * σ * g) := by
  have h1 := hx σ (Subgroup.mem_top σ) g (Subgroup.mem_top g)
  have h2 := hx g (Subgroup.mem_top g) (g⁻¹ * σ * g) (Subgroup.mem_top _)
  have hL : σ * g = g * (g⁻¹ * σ * g) := by group
  rw [hL] at h1
  rw [hσ, one_smul] at h1
  rw [h1] at h2
  exact add_right_cancel (by rw [h2, add_comm])

theorem inertiaVanishing_conj
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    {A B : ValuationSubring Ω} (hunrA : ¬ SSGRoute.IsRamifiedIn k K A)
    (hunrB : ¬ SSGRoute.IsRamifiedIn k K B)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ • A = B) :
    (∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A τ → b τ = 0) ↔
      ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ → b τ = 0 := by
  -- At a place unramified in `K`, every inertia element fixes `K`, hence is killed by the
  -- restriction `res k K : G_k →* Gal(K/k)`.
  have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  have hfixA : ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A τ → τ ∈ K.fixingSubgroup := by
    intro τ hτ
    by_contra hc
    exact hunrA ⟨τ, hτ, hc⟩
  have hfixB : ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ → τ ∈ K.fixingSubgroup := by
    intro τ hτ
    by_contra hc
    exact hunrB ⟨τ, hτ, hc⟩
  have hresA : ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A τ → SSGRoute.res k K τ = 1 :=
    fun τ hτ => MonoidHom.mem_ker.mp (hker ▸ hfixA τ hτ)
  have hresB : ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ → SSGRoute.res k K τ = 1 :=
    fun τ hτ => MonoidHom.mem_ker.mp (hker ▸ hfixB τ hτ)
  constructor
  · intro hA τ hτB
    -- `σ⁻¹ τ σ` is an inertia element of `A` (conjugation moves inertia groups).
    have his : SSGRoute.IsInertia k A (σ⁻¹ * τ * σ) :=
      (Work.SSGRoute.isInertia_conj A σ (σ⁻¹ * τ * σ)).mp (by
        have h2 : σ * (σ⁻¹ * τ * σ) * σ⁻¹ = τ := by group
        rw [h2, hσ]
        exact hτB)
    calc b τ = SSGRoute.res k K σ • b (σ⁻¹ * τ * σ) := cocycle_conj_eq hb (hresB τ hτB) σ
      _ = SSGRoute.res k K σ • 0 := by rw [hA _ his]
      _ = 0 := smul_zero _
  · intro hB τ hτA
    -- `σ τ σ⁻¹` is an inertia element of `B = σ • A`.
    have his : SSGRoute.IsInertia k B (σ * τ * σ⁻¹) := by
      have h1 : SSGRoute.IsInertia k (σ • A) (σ * τ * σ⁻¹) :=
        (Work.SSGRoute.isInertia_conj A σ τ).mpr hτA
      rwa [hσ] at h1
    calc b τ = SSGRoute.res k K σ⁻¹ • b ((σ⁻¹)⁻¹ * τ * σ⁻¹) :=
          cocycle_conj_eq hb (hresA τ hτA) σ⁻¹
      _ = SSGRoute.res k K σ⁻¹ • b (σ * τ * σ⁻¹) := by rw [inv_inv]
      _ = SSGRoute.res k K σ⁻¹ • 0 := by rw [hB _ his]
      _ = 0 := smul_zero _

end Work.SSGRoute.PT

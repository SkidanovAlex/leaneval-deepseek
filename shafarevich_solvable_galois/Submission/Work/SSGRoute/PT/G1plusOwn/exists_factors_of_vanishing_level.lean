import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.PT.exists_level_factors_locConstOn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

/-- **A cocycle vanishing on the intersection of the decomposition group with a level's fixing
subgroup factors through the restriction to that level.**

`b` a `1`-cocycle on `D_A = decomp k A` with values in the `Gal(K/k)`-module
`DualMod p (M ⊗ T)`, and `L ≤ Ω` a finite normal level over `k` on which `b` vanishes:
`b σ = 0` for every `σ ∈ D_A` fixing `L` pointwise (`hvan`).  Then `b|_D_A` factors through the
restriction map `AlgEquiv.restrictNormalHom L : G_k →* Gal(L/k)`.

Route: `b` is constant on the fibres of the restriction on `D_A`: if `σ, τ ∈ D_A` have the same
image in `Gal(L/k)`, then `σ⁻¹ τ ∈ D_A ⊓ L.fixingSubgroup` (`L.fixingSubgroup
= ker (AlgEquiv.restrictNormalHom L)`), so `b (σ⁻¹ τ) = 0` by `hvan`, and the cocycle identity
`hb` at `(σ, σ⁻¹ τ)` gives `b τ = b (σ * (σ⁻¹ τ)) = b σ + res(σ) • b (σ⁻¹ τ) = b σ`.
Then `b₀` is built by the `Classical.choose` pattern of
`Work.SSGRoute.PT.exists_level_factors_locConstOn`:
`b₀ τ := if ∃ σ ∈ D_A with restrictNormalHom L σ = τ then b (Classical.choose _) else 0`
(the values off the image of `D_A` are irrelevant). -/
theorem exists_factors_of_vanishing_level
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L]
    (hvan : ∀ σ ∈ SSGRoute.decomp k A, σ ∈ L.fixingSubgroup → b σ = 0) :
    ∃ b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ) := by
  -- `b` is constant on the fibres of the restriction map `D_A → Gal(L/k)`
  have hconst : ∀ σ ∈ SSGRoute.decomp k A, ∀ τ ∈ SSGRoute.decomp k A,
      AlgEquiv.restrictNormalHom L σ = AlgEquiv.restrictNormalHom L τ → b σ = b τ := by
    intro σ hσ τ hτ hres
    have hmemD : σ⁻¹ * τ ∈ SSGRoute.decomp k A := mul_mem (inv_mem hσ) hτ
    have hker : σ⁻¹ * τ ∈ L.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker (E := L)]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hres, inv_mul_cancel])
    have h0 : b (σ⁻¹ * τ) = 0 := hvan (σ⁻¹ * τ) hmemD hker
    have hb' := hb σ hσ (σ⁻¹ * τ) hmemD
    rw [mul_inv_cancel_left, h0, smul_zero, add_zero] at hb'
    exact hb'.symm
  -- a function constant on the fibres of a homomorphism factors through it
  classical
  refine ⟨fun τ => if h : ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A ∧
      AlgEquiv.restrictNormalHom L σ = τ then b h.choose else 0, ?_⟩
  intro σ hσ
  have hex : ∃ σ' : Ω ≃ₐ[k] Ω, σ' ∈ SSGRoute.decomp k A ∧
      AlgEquiv.restrictNormalHom L σ' = AlgEquiv.restrictNormalHom L σ := ⟨σ, hσ, rfl⟩
  show b σ = (if h : ∃ σ' : Ω ≃ₐ[k] Ω, σ' ∈ SSGRoute.decomp k A ∧
      AlgEquiv.restrictNormalHom L σ' = AlgEquiv.restrictNormalHom L σ
      then b h.choose else 0)
  rw [dif_pos hex]
  exact (hconst _ hex.choose_spec.1 σ hσ hex.choose_spec.2).symm

end Work.SSGRoute.PT.G1plusOwn

import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PT.exists_finiteNormal_fixingSubgroup_le_of_isOpen
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A common finite level for two locally constant cochains

Two locally constant cochains `a₁, a₂` on a subgroup `H ≤ G_k = Gal(Ω/k)` are simultaneously
inflated from a single finite normal level `L ⊇ K`: there are functions `aᵢ₀ : Gal(L/k) → Mᵢ`
with `aᵢ σ = aᵢ₀ (σ|_L)` for every `σ ∈ H`.

The argument is the one of `Work.SSGRoute.PT.exists_level_factors_locConstOn`, run with the
*intersection* of the two local-constancy subgroups: if `Uᵢ` witnesses `IsLocConstOn H aᵢ`, then
`U₁ ⊓ U₂` is open, so by Krull theory it contains the fixing subgroup of a finite normal level
`L ⊇ K`.  For `σ, τ ∈ H` with equal restriction to `L`, the element `σ⁻¹ τ` lies in
`L.fixingSubgroup ≤ Uᵢ ∩ H`, whence `aᵢ σ = aᵢ τ`; factoring each `aᵢ` through the restriction
homomorphism gives `aᵢ₀`.
-/

open SSGRoute
open Filter
open scoped Topology

namespace Work.SSGRoute.PT

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **Fibre-constancy factorisation.**  If `a : Gal(Ω/k) → M` is constant on the fibres of the
restriction `H → Gal(L/k)` — as guaranteed by a local-constancy subgroup `U ⊇ L.fixingSubgroup` —
then `a` factors through the restriction homomorphism. -/
theorem factors_of_fixingSubgroup_le
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {M : Type} [AddCommGroup M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [Normal k L] (U : Subgroup (Ω ≃ₐ[k] Ω))
    (hfix : L.fixingSubgroup ≤ U)
    (hU : ∀ g ∈ H, ∀ u ∈ U, u ∈ H → a (g * u) = a g) :
    ∃ a₀ : (L ≃ₐ[k] L) → M, ∀ σ ∈ H, a σ = a₀ (AlgEquiv.restrictNormalHom L σ) := by
  -- `a` is constant on the fibres of the restriction map `H → Gal(L/k)`.
  have hconst : ∀ σ ∈ H, ∀ τ ∈ H,
      AlgEquiv.restrictNormalHom L σ = AlgEquiv.restrictNormalHom L τ → a σ = a τ := by
    intro σ hσ τ hτ hres
    have hmemH : σ⁻¹ * τ ∈ H := mul_mem (inv_mem hσ) hτ
    have hker : σ⁻¹ * τ ∈ L.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker (E := L)]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hres, inv_mul_cancel])
    have h := hU σ hσ (σ⁻¹ * τ) (hfix hker) hmemH
    rw [mul_inv_cancel_left] at h
    exact h.symm
  -- A function constant on the fibres of a homomorphism on a subgroup factors through it.
  classical
  refine ⟨fun τ => if h : ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ H ∧
      AlgEquiv.restrictNormalHom L σ = τ then a h.choose else 0, ?_⟩
  intro σ hσ
  have hex : ∃ σ' : Ω ≃ₐ[k] Ω, σ' ∈ H ∧
      AlgEquiv.restrictNormalHom L σ' = AlgEquiv.restrictNormalHom L σ := ⟨σ, hσ, rfl⟩
  show a σ = (if h : ∃ σ' : Ω ≃ₐ[k] Ω, σ' ∈ H ∧
      AlgEquiv.restrictNormalHom L σ' = AlgEquiv.restrictNormalHom L σ
      then a h.choose else 0)
  rw [dif_pos hex]
  exact (hconst _ hex.choose_spec.1 σ hσ hex.choose_spec.2).symm

theorem exists_level_factors_locConstOnTwo
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    {M₁ M₂ : Type} [AddCommGroup M₁] [DistribMulAction (K ≃ₐ[k] K) M₁]
    [AddCommGroup M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a₁ : (Ω ≃ₐ[k] Ω) → M₁) (a₂ : (Ω ≃ₐ[k] Ω) → M₂)
    (h₁ : SSGRoute.IsLocConstOn H a₁) (h₂ : SSGRoute.IsLocConstOn H a₂) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : Normal k L),
      K ≤ L ∧ ∃ a₁₀ : (L ≃ₐ[k] L) → M₁, ∃ a₂₀ : (L ≃ₐ[k] L) → M₂,
        (∀ σ ∈ H, a₁ σ = a₁₀ (AlgEquiv.restrictNormalHom L σ)) ∧
        (∀ σ ∈ H, a₂ σ = a₂₀ (AlgEquiv.restrictNormalHom L σ)) := by
  obtain ⟨U₁, hU₁o, hU₁⟩ := h₁
  obtain ⟨U₂, hU₂o, hU₂⟩ := h₂
  -- the intersection of the two local-constancy subgroups is open
  have hUo : IsOpen (((U₁ ⊓ U₂ : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω))) :=
    hU₁o.inter hU₂o
  -- choose one finite normal level whose fixing subgroup lies in both
  obtain ⟨L, hLfin, hLnorm, hKL, hfixU⟩ :=
    exists_finiteNormal_fixingSubgroup_le_of_isOpen k Ω K (U₁ ⊓ U₂) hUo
  haveI : FiniteDimensional k L := hLfin
  haveI : Normal k L := hLnorm
  have hfixU₁ : L.fixingSubgroup ≤ U₁ := le_trans hfixU inf_le_left
  have hfixU₂ : L.fixingSubgroup ≤ U₂ := le_trans hfixU inf_le_right
  obtain ⟨a₁₀, ha₁₀⟩ := factors_of_fixingSubgroup_le H a₁ L U₁ hfixU₁ hU₁
  obtain ⟨a₂₀, ha₂₀⟩ := factors_of_fixingSubgroup_le H a₂ L U₂ hfixU₂ hU₂
  exact ⟨L, hLfin, hLnorm, hKL, a₁₀, a₂₀, ha₁₀, ha₂₀⟩

end Work.SSGRoute.PT

import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.exists_finiteNormal_fixingSubgroup_le_of_isOpen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finite-level factorisation of a locally constant cochain on a subgroup

A locally constant cochain `a` on a subgroup `H ≤ G_k = Gal(Ω/k)` (valued in any module `M`)
descends to a function on the Galois group of a *finite normal* level `L ⊇ K`: there is a finite
normal `L` with `K ≤ L` and a function `a₀ : Gal(L/k) → M` such that `a σ = a₀ (σ|_L)` for every
`σ ∈ H`.

This is the degree-`1` companion of `Work.SSGRoute.E7Fin.locConst2_factor_finiteLevel` (degree `2`)
and of `Work.SSGRoute.E7Fin.locConst_factor_finiteLevel`.  It is the "descent" half of the finite
level description

  `H¹_loc(H, M) = colim_L H¹(H / (H ∩ Gal(Ω/L)), M)`

of the locally constant cohomology on a subgroup of `G_k`: a locally constant cochain is inflated
from a finite quotient of `H`.

The proof is the standard one.  `IsLocConstOn H a` gives an *open* subgroup `U` of `G_k` such that
`a (g * u) = a g` for `g ∈ H` and `u ∈ U ∩ H`.  By the Krull topology the open subgroup
`U ⊓ Gal(Ω/K)` contains the fixing subgroup of some finite normal level `L₀ ⊇ K`
(`exists_finiteNormal_fixingSubgroup_le_of_isOpen`).  If `σ, τ ∈ H` have the same image in
`Gal(L₀/k)`, then `σ⁻¹ τ ∈ H ∩ Gal(Ω/L₀) ⊆ U ∩ H`, so `a τ = a (σ * (σ⁻¹ τ)) = a σ`: `a` is
constant on the fibres of the restriction map `H → Gal(L₀/k)`.  A function constant on the fibres
of a homomorphism on a subgroup factors through that homomorphism (`Classical.choose`), which
yields `a₀`.
-/

open SSGRoute
open Filter
open scoped Topology

namespace Work.SSGRoute.PT

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

theorem exists_level_factors_locConstOn
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (hH : SSGRoute.IsLocConstOn H a) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : Normal k L),
      K ≤ L ∧ ∃ a₀ : (L ≃ₐ[k] L) → M,
        ∀ σ ∈ H, a σ = a₀ (AlgEquiv.restrictNormalHom L σ) := by
  obtain ⟨U, hUopen, hU⟩ := hH
  -- a finite normal level above `K` whose fixing subgroup is contained in `U`
  obtain ⟨L, hfin, hnorm, hKL, hfixU⟩ :=
    exists_finiteNormal_fixingSubgroup_le_of_isOpen k Ω K U hUopen
  haveI : FiniteDimensional k L := hfin
  haveI : Normal k L := hnorm
  refine ⟨L, hfin, hnorm, hKL, ?_⟩
  -- `a` is constant on the fibres of the restriction map `H → Gal(L/k)`
  have hconst : ∀ σ ∈ H, ∀ τ ∈ H,
      AlgEquiv.restrictNormalHom L σ = AlgEquiv.restrictNormalHom L τ → a σ = a τ := by
    intro σ hσ τ hτ hres
    have hmemH : σ⁻¹ * τ ∈ H := mul_mem (inv_mem hσ) hτ
    have hker : σ⁻¹ * τ ∈ L.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker (E := L)]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hres, inv_mul_cancel])
    have hU' : σ⁻¹ * τ ∈ U := hfixU hker
    have h := hU σ hσ (σ⁻¹ * τ) hU' hmemH
    rw [mul_inv_cancel_left] at h
    exact h.symm
  -- a function constant on the fibres of a homomorphism factors through it
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

end Work.SSGRoute.PT

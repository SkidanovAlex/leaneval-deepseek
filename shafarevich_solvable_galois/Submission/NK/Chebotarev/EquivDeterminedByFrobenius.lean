import Mathlib
import Submission.NK.Chebotarev.FrobeniusGenerateTop
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Chebotarev

/-- **An isomorphism of Galois groups is determined by its values on Frobenius elements.**

`FrobeniusGenerateTop` says that the Frobenius elements at the finite places of `K` generate
`Gal(L₁/K)` as a group.  Hence two group isomorphisms `Gal(L₁/K) ≃* Gal(L₂/K)` which agree on
every Frobenius element agree everywhere. -/
theorem EquivDeterminedByFrobenius {K L₁ L₂ : Type*} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] [IsGalois K L₁] [IsGalois K L₂]
    (φ ψ : Gal(L₁/K) ≃* Gal(L₂/K))
    (h : ∀ σ : Gal(L₁/K), (∃ p : NK.Chebotarev.PrimeIdeal K,
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L₁) p σ) → φ σ = ψ σ) :
    φ = ψ := by
  -- The set of Frobenius elements generates `Gal(L₁/K)`.
  have hmem : ∀ σ : Gal(L₁/K), φ σ = ψ σ := by
    intro σ
    have hσ : σ ∈ Subgroup.closure ({σ : Gal(L₁/K) | ∃ p : NK.Chebotarev.PrimeIdeal K,
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L₁) p σ} : Set Gal(L₁/K)) := by
      rw [FrobeniusGenerateTop (K := K) (L := L₁)]
      exact Subgroup.mem_top σ
    induction hσ using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => simp
    | mul x y hx hy ihx ihy => rw [map_mul, map_mul, ihx, ihy]
    | inv x hx ih => rw [map_inv, map_inv, ih]
  exact MulEquiv.ext hmem

end NK.Chebotarev

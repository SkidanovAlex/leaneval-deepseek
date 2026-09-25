import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace Commons.FieldTheory.Galois

open scoped Pointwise

/-- **The trace on a normal intermediate field of the image of a valuation subring is the image
of its trace**: `(σ • A) ∩ L = σ|_L • (A ∩ L)`.

Suggested route: `ValuationSubring.smul_eq_comap_symm` (or its `≃+*` form) rewrites both sides as
preimages, `ValuationSubring.comap_comap` composes the ring homomorphisms, and
`AlgEquiv.restrictNormal_commutes` identifies `σ.symm ∘ algebraMap L K'` with
`algebraMap L K' ∘ (σ|_L).symm`. -/
theorem comap_smul_eq_restrictNormalHom_smul {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (A : ValuationSubring K') (σ : K' ≃ₐ[K] K') (L : IntermediateField K K') [Normal K L] :
    (σ • A).comap (algebraMap ↥L K') =
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ) • (A.comap (algebraMap ↥L K')) := by
  ext x
  simp only [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rw [show (σ⁻¹ : K' ≃ₐ[K] K') = σ.symm from rfl]
  rw [show ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ)⁻¹ : ↥L ≃ₐ[K] ↥L)
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ.symm from
        (map_inv (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L) σ).symm]
  change σ.symm (algebraMap ↥L K' x) ∈ A ↔
      algebraMap ↥L K' ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L) σ.symm x) ∈ A
  rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L) σ.symm
      = (σ.symm).restrictNormal L from rfl]
  rw [AlgEquiv.restrictNormal_commutes]

end Commons.FieldTheory.Galois
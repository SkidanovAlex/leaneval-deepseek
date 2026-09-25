import Mathlib

namespace NK.Reconstruct

open scoped Pointwise in
/-- **The trace on a normal subfield of the image of a valuation subring is the image of its
trace**, in the general (algebra) form: for a normal extension `E/F` sitting inside `K/F` through a
scalar tower `F → E → K`, the restriction to `E` of the image of `A : ValuationSubring K` under
`σ : K ≃ₐ[F] K` is the image of the trace `A ∩ E` under the restriction `σ|_E`.

This is the general-algebra restatement of
`Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul` (which is stated for an
intermediate field `L ≤ K`); the proof is the same, using
`AlgEquiv.restrictNormal_commutes` for the general `E`. -/
theorem comap_smul_eq_restrictNormalHom_smul_type {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K] [Normal F E]
    (A : ValuationSubring K) (σ : K ≃ₐ[F] K) :
    (σ • A).comap (algebraMap E K) =
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E σ) • (A.comap (algebraMap E K)) := by
  ext x
  simp only [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rw [show (σ⁻¹ : K ≃ₐ[F] K) = σ.symm from rfl]
  rw [show ((AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E σ)⁻¹ : E ≃ₐ[F] E)
      = AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E σ.symm from
        (map_inv (AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E) σ).symm]
  change σ.symm (algebraMap E K x) ∈ A ↔
      algebraMap E K ((AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E) σ.symm x) ∈ A
  rw [show (AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E) σ.symm
      = (σ.symm).restrictNormal E from rfl]
  rw [AlgEquiv.restrictNormal_commutes]

end NK.Reconstruct

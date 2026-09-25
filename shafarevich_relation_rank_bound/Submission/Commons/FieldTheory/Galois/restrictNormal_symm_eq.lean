import Mathlib.FieldTheory.Normal.Defs

namespace Commons.FieldTheory.Galois

/-- The restriction of `σ⁻¹` to a normal intermediate field is the inverse of the restriction of
`σ`. -/
theorem restrictNormal_symm_eq {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (σ : K' ≃ₐ[K] K') (L : IntermediateField K K') [Normal K L] :
    (σ.symm).restrictNormal L = (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ).symm := by
  change (σ.symm).restrictNormal L = (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ)⁻¹
  rw [← map_inv]
  rfl

end Commons.FieldTheory.Galois
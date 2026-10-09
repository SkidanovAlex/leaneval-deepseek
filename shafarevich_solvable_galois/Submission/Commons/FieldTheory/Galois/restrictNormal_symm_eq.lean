import Mathlib.FieldTheory.Normal.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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
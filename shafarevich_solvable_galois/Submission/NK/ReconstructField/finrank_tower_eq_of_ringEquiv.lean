import Mathlib.LinearAlgebra.Dimension.Finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

/-- **Degree is invariant under an isomorphism of field extensions.**

If `σ : E ≃+* E'` and `τ : L ≃+* L'` are ring isomorphisms compatible with the
structure maps (`σ (algebraMap L E x) = algebraMap L' E' (τ x)` for all `x`), then
`E` and `E'` have the same degree over `L` and `L'` respectively.

This is the scalar-restriction invariance of the dimension: `σ` becomes an
`L`-linear equivalence `E ≃ₗ[L] E'` when the `L`-action on `E'` is pulled back
along `τ`, and `Module.finrank` only depends on the isomorphism class of the
scalars.  Formally it is the `ℕ`-valued shadow of
`Algebra.rank_eq_of_equiv_equiv` (the corresponding cardinal identity),
available in Mathlib as `Algebra.finrank_eq_of_equiv_equiv`. -/
theorem finrank_tower_eq_of_ringEquiv {K L E K' L' E' : Type*} [Field K] [Field L] [Field E]
    [Field K'] [Field L'] [Field E'] [Algebra K L] [Algebra L E] [Algebra K E]
    [IsScalarTower K L E] [Algebra K' L'] [Algebra L' E'] [Algebra K' E'] [IsScalarTower K' L' E']
    (σ : E ≃+* E') (τ : L ≃+* L')
    (h : ∀ x : L, σ (algebraMap L E x) = algebraMap L' E' (τ x)) :
    Module.finrank L E = Module.finrank L' E' := by
  apply Algebra.finrank_eq_of_equiv_equiv τ σ
  ext x
  simp only [RingHom.comp_apply]
  exact (h x).symm

end NK.ReconstructField

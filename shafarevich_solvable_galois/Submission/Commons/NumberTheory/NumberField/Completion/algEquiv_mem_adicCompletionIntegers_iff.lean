import Mathlib.RingTheory.DedekindDomain.AdicValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

/-- Every `v.adicCompletion K`-algebra automorphism of the `v`-adic completion `v.adicCompletion K`
preserves its ring of integers `v.adicCompletionIntegers K`.

Note that an `R`-algebra automorphism of `R` itself is necessarily the identity: the `commutes'`
field of `AlgEquiv` gives `σ (algebraMap R R x) = algebraMap R R x`, and the structure map
`algebraMap R R` of the canonical algebra structure on `R` over itself is the identity. Hence
`σ x = x` for every `x`, and in particular membership in any subset (here the subring
`v.adicCompletionIntegers K`) is preserved. -/
theorem algEquiv_mem_adicCompletionIntegers_iff (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (σ : v.adicCompletion K ≃ₐ[v.adicCompletion K] v.adicCompletion K)
    (x : v.adicCompletion K) :
    σ x ∈ v.adicCompletionIntegers K ↔ x ∈ v.adicCompletionIntegers K := by
  have hx : σ x = x := σ.commutes x
  rw [hx]

end Commons.NumberTheory.NumberField.Completion
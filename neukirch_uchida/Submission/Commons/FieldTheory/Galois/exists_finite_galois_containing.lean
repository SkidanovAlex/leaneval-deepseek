import Mathlib.FieldTheory.Galois.Basic

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

open IntermediateField

/-- In a (possibly infinite) Galois extension `K/k`, every element of `K` is contained in a
finite-dimensional intermediate field that is Galois over `k`.

Indeed, `x` is algebraic over `k`, so `L₀ := k⟮x⟯` is finite-dimensional; its normal closure
`normalClosure k L₀ K` inside `K` is then finite-dimensional, normal, and separable (as `K/k` is
separable), hence Galois over `k`, and it contains `L₀` and therefore `x`. -/
theorem exists_finite_galois_containing {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (x : K) : ∃ L : IntermediateField k K, FiniteDimensional k L ∧ IsGalois k L ∧ x ∈ L := by
  have hx : IsIntegral k x := IsGalois.integral k x
  let L₀ : IntermediateField k K := k⟮x⟯
  haveI hL₀ : FiniteDimensional k L₀ := IntermediateField.adjoin.finiteDimensional hx
  refine ⟨IntermediateField.normalClosure k L₀ K, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · exact IntermediateField.le_normalClosure L₀ (IntermediateField.mem_adjoin_simple_self k x)

end Commons.FieldTheory.Galois
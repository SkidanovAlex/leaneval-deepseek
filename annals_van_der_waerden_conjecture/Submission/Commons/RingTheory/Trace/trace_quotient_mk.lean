import Mathlib.RingTheory.Trace.Basic

namespace Commons.RingTheory.Trace

open TensorProduct

theorem trace_quotient_mk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (I : Ideal R) (x : S) :
    Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S))
        (Ideal.Quotient.mk (I.map (algebraMap R S)) x) =
      Ideal.Quotient.mk I (Algebra.trace R S x) := by
  have hlmul : Algebra.lmul (R ⧸ I) (TensorProduct R (R ⧸ I) S) (1 ⊗ₜ[R] x) =
      LinearMap.baseChange (R ⧸ I) (Algebra.lmul R S x) := by
    apply AlgebraTensorModule.ext
    intro a s
    change (1 ⊗ₜ[R] x) * (a ⊗ₜ[R] s) =
      LinearMap.baseChange (R ⧸ I) (Algebra.lmul R S x) (a ⊗ₜ[R] s)
    rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul]
    simp
  have key : Algebra.trace (R ⧸ I) (TensorProduct R (R ⧸ I) S) (1 ⊗ₜ[R] x) =
      Ideal.Quotient.mk I (Algebra.trace R S x) := by
    rw [Algebra.trace_apply, hlmul, LinearMap.trace_baseChange, ← Algebra.trace_apply,
      Ideal.Quotient.algebraMap_eq]
  rw [← key]
  rw [← Algebra.trace_eq_of_algEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I)
    (Ideal.Quotient.mk (I.map (algebraMap R S)) x)]
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]

end Commons.RingTheory.Trace
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace Commons.RingTheory.Valuation

open scoped Pointwise

/-- **Elementwise description of the stabiliser of a valuation subring.**  For a field extension
`E / F` and a valuation subring `A` of `E`, an `F`-algebra automorphism `σ` stabilises `A` if and
only if `σ x ∈ A ↔ x ∈ A` for every `x : E`.  (The stabiliser is taken for the pointwise action of
`E ≃ₐ[F] E` on `ValuationSubring E`, available in the `Pointwise` locale.) -/
theorem mem_stabilizer_valuationSubring_iff {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : E ≃ₐ[F] E) :
    σ ∈ MulAction.stabilizer (E ≃ₐ[F] E) A ↔ ∀ x : E, (x ∈ A ↔ σ x ∈ A) := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    have h1 := (SetLike.ext_iff.mp h) (σ x)
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at h1
    simpa using h1
  · intro h
    rw [SetLike.ext_iff]
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using h (σ⁻¹ x)

end Commons.RingTheory.Valuation
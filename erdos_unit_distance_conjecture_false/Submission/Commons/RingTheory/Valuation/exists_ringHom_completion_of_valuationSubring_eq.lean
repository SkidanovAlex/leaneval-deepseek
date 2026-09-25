import Mathlib.Topology.Algebra.Valued.WithVal

open Valuation

namespace Commons.RingTheory.Valuation

/-- Two valuations `v` and `w` on a field `K` with the same valuation subring induce the same
valuation topology on `K`, hence their completions are canonically isomorphic as topological
rings via a map compatible with the embeddings of `K`.

Proof: the equality of valuation subrings gives `v.IsEquiv w`
(`Valuation.isEquiv_iff_val_le_one`), hence the ring equivalence
`WithVal.congr v w (RingEquiv.refl K)` is a uniform isomorphism of `WithVal v` and `WithVal w`.
Lifting it to the completions via `UniformSpace.Completion.mapRingEquiv` yields the wanted
bijective ring homomorphism, and the compatibility with the embeddings of `K` follows from
`UniformSpace.Completion.mapRingEquiv_apply` and `UniformSpace.Completion.map_coe`. -/
theorem exists_ringHom_completion_of_valuationSubring_eq {K : Type*} [Field K] {Γ₀ Γ₁ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (v : Valuation K Γ₀) (w : Valuation K Γ₁) (h : v.valuationSubring = w.valuationSubring) :
    ∃ φ : v.Completion →+* w.Completion, Function.Bijective φ ∧ ∀ x : K,
      φ (x : v.Completion) = (x : w.Completion) := by
  -- The two valuations have the same unit ball, so they are equivalent valuations.
  have hv : v.IsEquiv w := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [← Valuation.mem_valuationSubring_iff v x, h, Valuation.mem_valuationSubring_iff w x]
  -- The identity on `K` induces a uniform isomorphism `WithVal v ≃ WithVal w`.
  let e : WithVal v ≃+* WithVal w := WithVal.congr v w (RingEquiv.refl K)
  have huc : UniformContinuous (e : WithVal v → WithVal w) := hv.uniformContinuous_congr
  have huc' : UniformContinuous (e.symm : WithVal w → WithVal v) :=
    hv.symm.uniformContinuous_congr
  -- Lift it to a ring isomorphism of the completions.
  refine ⟨UniformSpace.Completion.mapRingEquiv e huc.continuous huc'.continuous, ?_, ?_⟩
  · exact (UniformSpace.Completion.mapRingEquiv e huc.continuous huc'.continuous).bijective
  · intro x
    change UniformSpace.Completion.mapRingEquiv e huc.continuous huc'.continuous
      (x : v.Completion) = (x : w.Completion)
    rw [UniformSpace.Completion.mapRingEquiv_apply]
    rw [show (x : v.Completion)
        = ((WithVal.toVal v x : WithVal v) : UniformSpace.Completion (WithVal v)) from rfl]
    rw [UniformSpace.Completion.map_coe huc]
    rw [show (x : w.Completion)
        = ((WithVal.toVal w x : WithVal w) : UniformSpace.Completion (WithVal w)) from rfl]
    congr 1

end Commons.RingTheory.Valuation
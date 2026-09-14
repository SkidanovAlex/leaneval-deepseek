import Mathlib

namespace Commons.FieldTheory.Galois

theorem prod_algHom_map_algEquiv {L K : Type*} [Field L] [Field K] [Algebra ℚ L] [Algebra ℚ K]
    [FiniteDimensional ℚ L] [FiniteDimensional ℚ K] [Fintype (L →ₐ[ℚ] ℂ)] [Fintype (K →ₐ[ℚ] ℂ)]
    (e : L ≃ₐ[ℚ] K) (P : Polynomial L) :
    (∏ ψ : (K →ₐ[ℚ] ℂ), (P.map e.toRingHom).map ψ.toRingHom)
      = ∏ χ : (L →ₐ[ℚ] ℂ), P.map χ.toRingHom := by
  classical
  refine Fintype.prod_bijective (fun ψ : K →ₐ[ℚ] ℂ => ψ.comp (e : L →ₐ[ℚ] K)) ?_ _ _ ?_
  · -- the map ψ ↦ ψ ∘ e is a bijection
    refine ⟨?_, ?_⟩
    · intro ψ₁ ψ₂ h
      have := congrArg (fun χ : L →ₐ[ℚ] ℂ => χ.comp (e.symm : K →ₐ[ℚ] L)) h
      simpa [AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.comp_id] using this
    · intro χ
      exact ⟨χ.comp (e.symm : K →ₐ[ℚ] L), by
        simp [AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.comp_id]⟩
  · -- pointwise identity
    intro ψ
    rw [Polynomial.map_map]
    congr 1

end Commons.FieldTheory.Galois

import Mathlib
import Submission.Work.Drive.TripleMeetDefs

/-!
# `TripleTransverse` is invariant under composing with continuous linear equivalences

`Work.Drive.TripleTransverse f₀ f₁ f₂` (`Submission/Work/Drive/TripleMeetDefs.lean`) says that the
difference map `(v₀,v₁,v₂) ↦ (f₀v₀ - f₁v₁, f₀v₀ - f₂v₂)` is surjective.  Since a continuous linear
equivalence `L` of the target is bijective and one `M` of the source is surjective, both the
surjectivity and its failure are unchanged by pre- and post-composing the three maps:
`TripleTransverse (L ∘ fᵢ ∘ M)ᵢ ↔ TripleTransverse (fᵢ)ᵢ`.

This is the chart-independence of the transversality condition: it lets one check transversality of
three `3`-chains in a `4`-manifold in whichever linear coordinates are convenient.
-/

namespace Work.Drive

theorem tripleTransverse_comp_continuousLinearEquiv
    (L : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3))
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    Work.Drive.TripleTransverse ((L : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp
        (f₀.comp (M : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))))
      ((L : _ →L[ℝ] _).comp (f₁.comp (M : _ →L[ℝ] _)))
      ((L : _ →L[ℝ] _).comp (f₂.comp (M : _ →L[ℝ] _))) ↔
    Work.Drive.TripleTransverse f₀ f₁ f₂ := by
  constructor
  · -- the composed maps are transverse, hence so are the originals: solve with `L wᵢ` and apply `M`
    intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (L w₁) (L w₂)
    refine ⟨fun i => M (v i), ?_, ?_⟩
    · apply L.injective
      rw [map_sub]
      exact h1
    · apply L.injective
      rw [map_sub]
      exact h2
  · -- the originals are transverse, hence so are the composed ones: solve with `L.symm wᵢ` and
    -- apply `M.symm`
    intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (L.symm w₁) (L.symm w₂)
    refine ⟨fun i => M.symm (v i), ?_, ?_⟩
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, M.apply_symm_apply]
      rw [← map_sub, h1, L.apply_symm_apply]
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, M.apply_symm_apply]
      rw [← map_sub, h2, L.apply_symm_apply]

end Work.Drive

import Mathlib
import Submission.Work.Drive.TripleGeneral

/-!
# Invariance of the `E`-valued transversality under an isomorphism of one factor

`Work.Drive.TripleTransverseE` for maps with values in a *product* is invariant under post-composing
the first factor with a linear isomorphism.  This is the statement that lets the identification
`chart₁ = logEucl ∘ log` (`Work.Drive.eventuallyEq_chartAt_expHomeo`) be used on the first component of
the chart derivative of a radial sweep, whose target is `ℝ¹ × ℝP³ = ℝ × ℝ³`.
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

theorem tripleTransverseE_prod_comp_continuousLinearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ψ : E ≃L[ℝ] E') (f : Fin 3 → EuclideanSpace ℝ (Fin 3) →L[ℝ] E)
    (g : Fin 3 → EuclideanSpace ℝ (Fin 3) →L[ℝ] G) :
    TripleTransverseE
      (((Ψ : E →L[ℝ] E').comp (f 0)).prod (g 0))
      (((Ψ : E →L[ℝ] E').comp (f 1)).prod (g 1))
      (((Ψ : E →L[ℝ] E').comp (f 2)).prod (g 2))
      ↔ TripleTransverseE ((f 0).prod (g 0)) ((f 1).prod (g 1)) ((f 2).prod (g 2)) := by
  constructor
  · intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (Ψ w₁.1, w₁.2) (Ψ w₂.1, w₂.2)
    have h1a : (Ψ : E →L[ℝ] E') (f 0 (v 0)) - Ψ (f 1 (v 1)) = Ψ w₁.1 := by
      have := congrArg Prod.fst h1
      simpa using this
    have h1b : g 0 (v 0) - g 1 (v 1) = w₁.2 := by
      have := congrArg Prod.snd h1
      simpa using this
    have h2a : (Ψ : E →L[ℝ] E') (f 0 (v 0)) - Ψ (f 2 (v 2)) = Ψ w₂.1 := by
      have := congrArg Prod.fst h2
      simpa using this
    have h2b : g 0 (v 0) - g 2 (v 2) = w₂.2 := by
      have := congrArg Prod.snd h2
      simpa using this
    refine ⟨v, Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩
    · refine Ψ.injective ?_
      simp only [Prod.fst_sub, ContinuousLinearMap.prod_apply]
      rw [map_sub]
      exact h1a
    · simp only [Prod.snd_sub, ContinuousLinearMap.prod_apply]
      exact h1b
    · refine Ψ.injective ?_
      simp only [Prod.fst_sub, ContinuousLinearMap.prod_apply]
      rw [map_sub]
      exact h2a
    · simp only [Prod.snd_sub, ContinuousLinearMap.prod_apply]
      exact h2b
  · intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (Ψ.symm w₁.1, w₁.2) (Ψ.symm w₂.1, w₂.2)
    have h1a : f 0 (v 0) - f 1 (v 1) = Ψ.symm w₁.1 := by
      have := congrArg Prod.fst h1
      simpa using this
    have h1b : g 0 (v 0) - g 1 (v 1) = w₁.2 := by
      have := congrArg Prod.snd h1
      simpa using this
    have h2a : f 0 (v 0) - f 2 (v 2) = Ψ.symm w₂.1 := by
      have := congrArg Prod.fst h2
      simpa using this
    have h2b : g 0 (v 0) - g 2 (v 2) = w₂.2 := by
      have := congrArg Prod.snd h2
      simpa using this
    refine ⟨v, Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩
    · simp only [Prod.fst_sub, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
      rw [← map_sub, h1a]
      exact Ψ.apply_symm_apply w₁.1
    · simp only [Prod.snd_sub, ContinuousLinearMap.prod_apply]
      exact h1b
    · simp only [Prod.fst_sub, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
      rw [← map_sub, h2a]
      exact Ψ.apply_symm_apply w₂.1
    · simp only [Prod.snd_sub, ContinuousLinearMap.prod_apply]
      exact h2b

end

end Work.Drive

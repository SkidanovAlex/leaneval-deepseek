import Mathlib

namespace Work.Embedding

/-- A uniform bound for the second Fréchet derivative of a `C²` map on a compact set. -/
theorem uniform_bound_fderiv_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ψ : E → F} {s : Set E} (hs : IsCompact s)
    (hψ : ∀ u ∈ s, ContDiffAt ℝ 2 ψ u) :
    ∃ C, 0 < C ∧ ∀ u ∈ s, ∀ d₁ d₂ : E,
      ‖(fderiv ℝ (fderiv ℝ ψ) u) d₁ d₂‖ ≤ C * ‖d₁‖ * ‖d₂‖ := by
  -- At each point of `s` the second derivative is the derivative of `fderiv ℝ ψ`,
  -- which is the `fderiv` of a `C¹` map, hence continuous there.
  have hcont : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ ψ) x‖) s := by
    intro u hu
    exact ((((hψ u hu).fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv
      (by norm_num)).norm).continuousWithinAt
  -- The norm of the second derivative is bounded on the compact image.
  obtain ⟨R, hRpos, hR⟩ := (hs.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨R, hRpos, fun u hu d₁ d₂ => ?_⟩
  have hgu : ‖fderiv ℝ (fderiv ℝ ψ) u‖ ≤ R := by
    have h := hR (‖fderiv ℝ (fderiv ℝ ψ) u‖) (Set.mem_image_of_mem _ hu)
    rwa [Real.norm_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ ψ) u))] at h
  -- Chain the two operator-norm estimates.
  have step1 : ‖(fderiv ℝ (fderiv ℝ ψ) u) d₁ d₂‖
      ≤ ‖fderiv ℝ (fderiv ℝ ψ) u‖ * ‖d₁‖ * ‖d₂‖ := by
    calc ‖(fderiv ℝ (fderiv ℝ ψ) u) d₁ d₂‖
        ≤ ‖(fderiv ℝ (fderiv ℝ ψ) u) d₁‖ * ‖d₂‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ ψ) u‖ * ‖d₁‖) * ‖d₂‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fderiv ℝ ψ) u‖ * ‖d₁‖ * ‖d₂‖ := by ring
  refine step1.trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right hgu (norm_nonneg _)

end Work.Embedding

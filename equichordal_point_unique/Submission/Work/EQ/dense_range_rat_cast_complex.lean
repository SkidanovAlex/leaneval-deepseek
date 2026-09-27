import Mathlib

namespace Work.EQ

/-- The set of Gaussian rationals `{a + b i : a b : ℚ}` is dense in `ℂ`.

This is the two-dimensional form of the density of `ℚ` in `ℝ`: the diagonal map
`ℚ × ℚ → ℝ × ℝ` has dense range, and the canonical homeomorphism
`ℂ ≃ ℝ × ℝ` (given by `z ↦ (z.re, z.im)`, whose inverse is `p ↦ p.1 + p.2 * I`)
transports density. -/
theorem dense_range_rat_cast_complex :
    Dense (Set.range (fun x : ℚ × ℚ => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I)) := by
  -- `ℚ × ℚ` maps with dense range to `ℝ × ℝ`.
  have hf : DenseRange (fun x : ℚ × ℚ => ((x.1 : ℝ), (x.2 : ℝ))) :=
    DenseRange.prodMap Rat.denseRange_cast Rat.denseRange_cast
  -- The inverse of the canonical homeomorphism `ℂ ≃ ℝ × ℝ` is surjective.
  have hg : DenseRange Complex.equivRealProdCLM.symm :=
    Complex.equivRealProdCLM.symm.surjective.denseRange
  -- Compose, using continuity of the homeomorphism.
  have h := hg.comp hf Complex.equivRealProdCLM.symm.continuous
  have heq : (Complex.equivRealProdCLM.symm ∘ (fun x : ℚ × ℚ => ((x.1 : ℝ), (x.2 : ℝ))))
      = (fun x : ℚ × ℚ => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I) := by
    funext x
    simp [Complex.equivRealProdCLM_symm_apply]
  rwa [heq] at h

end Work.EQ

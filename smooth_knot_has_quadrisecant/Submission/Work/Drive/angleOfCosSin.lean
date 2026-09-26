import Mathlib
import Submission.Work.Drive.framePathDefs

namespace Work.Drive

/-- `angleOf p q` is the argument of the unit complex number `p + i q`, hence its
cosine is `p` and its sine is `q` whenever `p ^ 2 + q ^ 2 = 1`. -/
theorem angleOfCosSin {p q : ℝ} (h : p ^ 2 + q ^ 2 = 1) :
    Real.cos (Work.Drive.angleOf p q) = p ∧ Real.sin (Work.Drive.angleOf p q) = q := by
  -- `p + i q` has norm `1`, so it is nonzero and `Complex.cos_arg`/`Complex.sin_arg`
  -- give the cosine and sine of its argument as `re / ‖·‖` and `im / ‖·‖`.
  have hs : ‖(⟨p, q⟩ : ℂ)‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [h, sq_nonneg p, sq_nonneg q]
  have hnorm : ‖(⟨p, q⟩ : ℂ)‖ = 1 := by nlinarith [norm_nonneg (⟨p, q⟩ : ℂ)]
  have hne : (⟨p, q⟩ : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hs
    norm_num at hs
  constructor
  · rw [Work.Drive.angleOf, Complex.cos_arg hne, hnorm, div_one]
  · rw [Work.Drive.angleOf, Complex.sin_arg, hnorm, div_one]

end Work.Drive

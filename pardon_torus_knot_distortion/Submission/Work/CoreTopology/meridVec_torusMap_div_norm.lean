import Mathlib
import Submission.Work.CoreTopology.TorusDichotomyDefs

namespace Work.CoreTopology

noncomputable section

/-! ## The coordinates of a point of the parametrised torus -/

@[simp] theorem torusMap_apply_zero (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) 0 = (2 + Real.cos φ) * Real.cos θ := by
  simp [Work.Core.torusMap]

@[simp] theorem torusMap_apply_one (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) 1 = (2 + Real.cos φ) * Real.sin θ := by
  simp [Work.Core.torusMap]

@[simp] theorem torusMap_apply_two (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) 2 = Real.sin φ := by
  simp [Work.Core.torusMap]

/-- The squared horizontal radius of a point of the parametrised torus is `(2 + cos φ)²`. -/
theorem horizRadiusSq_torusMap (θ φ : ℝ) :
    horizRadiusSq (Work.Core.torusMap θ φ) = (2 + Real.cos φ) ^ 2 := by
  rw [horizRadiusSq, torusMap_apply_zero, torusMap_apply_one]
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- The horizontal radius of a point of the parametrised torus is `2 + cos φ` (which is
`> 0`, the minor radius of the torus about the axis). -/
theorem horizRadius_torusMap (θ φ : ℝ) :
    horizRadius (Work.Core.torusMap θ φ) = 2 + Real.cos φ := by
  rw [horizRadius, horizRadiusSq_torusMap, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by linarith [Real.neg_one_le_cos φ])]

/-- `exp (i φ) = (cos φ, sin φ)` as a complex number. -/
theorem exp_mul_I_eq (φ : ℝ) :
    Complex.exp ((φ : ℂ) * Complex.I) = (⟨Real.cos φ, Real.sin φ⟩ : ℂ) := by
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_im]

/-- The meridian projection of a point of the parametrised torus is exactly `exp (i φ)`. -/
theorem meridVec_torusMap (θ φ : ℝ) :
    meridVec (Work.Core.torusMap θ φ) = Complex.exp ((φ : ℂ) * Complex.I) := by
  rw [exp_mul_I_eq]
  apply Complex.ext <;> simp [meridVec, horizRadius_torusMap]

/-- **The meridian projection of a point of the standard torus is `exp (i φ)`.**  For all `θ φ`,
`meridVec (torusMap θ φ) / ‖meridVec (torusMap θ φ)‖ = exp (i φ)`; in fact
`meridVec (torusMap θ φ) = exp (i φ)` itself already has modulus one. -/
theorem meridVec_torusMap_div_norm (θ φ : ℝ) :
    meridVec (Work.Core.torusMap θ φ) / ((‖meridVec (Work.Core.torusMap θ φ)‖ : ℝ) : ℂ) =
      Complex.exp ((φ : ℂ) * Complex.I) := by
  rw [meridVec_torusMap, Complex.norm_exp_ofReal_mul_I]
  simp

end

end Work.CoreTopology

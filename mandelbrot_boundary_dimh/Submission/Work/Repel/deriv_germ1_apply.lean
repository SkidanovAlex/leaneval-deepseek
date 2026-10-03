import Mathlib
import Submission.Work.Repel.Spec

namespace Work.Repel

/-- The rescaled pushdown `germ1 s R = ζ ↦ s · pushdown R (ζ/s)` has, at every point `ζ`, the
derivative of `pushdown R` at `ζ/s`; the rescaling by `s` and the pre-composition with `ζ ↦ ζ/s`
cancel.  No differentiability is needed: `deriv` is `0` at points where the function is not
differentiable, and `ζ ↦ ζ/s` and `w ↦ s·w` are inverse affine bijections. -/
theorem deriv_germ1_apply (R : ℂ → ℂ) (s : ℂ) (hs : s ≠ 0) (ζ : ℂ) :
    deriv (Work.Repel.germ1 s R) ζ = deriv (MandelDim.pushdown R) (ζ / s) := by
  have hfun : Work.Repel.germ1 s R = (fun ζ => s * MandelDim.pushdown R (s⁻¹ * ζ)) := by
    funext ζ
    rw [Work.Repel.germ1_apply, div_eq_inv_mul]
  rw [hfun, deriv_const_mul_field, deriv_comp_mul_left]
  simp only [smul_eq_mul, div_eq_inv_mul]
  exact mul_inv_cancel_left₀ hs _

end Work.Repel

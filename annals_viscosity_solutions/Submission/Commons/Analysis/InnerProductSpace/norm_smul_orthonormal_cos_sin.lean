import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace

namespace Commons.Analysis.InnerProductSpace

theorem norm_smul_orthonormal_cos_sin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) (a rho theta : ℝ) :
    ‖a • e - rho • (Real.cos theta • e + Real.sin theta • f)‖
      = Real.sqrt ((a - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2) := by
  have hx : a • e - rho • (Real.cos theta • e + Real.sin theta • f)
      = (a - rho * Real.cos theta) • e + (-(rho * Real.sin theta)) • f := by
    simp only [smul_add, smul_smul]
    module
  have hsq : ‖a • e - rho • (Real.cos theta • e + Real.sin theta • f)‖ ^ 2
      = (a - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2 := by
    rw [hx]
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm, hef, he, hf,
      starRingEnd_apply, star_trivial]
    ring
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at this

end Commons.Analysis.InnerProductSpace
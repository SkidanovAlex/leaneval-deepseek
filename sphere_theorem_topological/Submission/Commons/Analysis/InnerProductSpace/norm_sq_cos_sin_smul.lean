import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.InnerProductSpace

/-- For an orthonormal triple `N, e, f` (with `N, e` unit and all pairwise orthogonal)
the squared norm of `-(sin r * r') • N + (cos r * r') • e + sin r • f` equals
`r' ^ 2 + (sin r) ^ 2 * ‖f‖ ^ 2`. -/
theorem norm_sq_cos_sin_smul {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (N e f : F) (r r' : ℝ)
    (hN : norm N = 1) (hNe : inner ℝ N e = 0) (hNf : inner ℝ N f = 0)
    (he : norm e = 1) (hef : inner ℝ e f = 0) :
    norm (-(Real.sin r * r') • N + (Real.cos r * r') • e + Real.sin r • f) ^ 2 = r' ^ 2 + (Real.sin r) ^ 2 * norm f ^ 2 := by
  have hinner :
      inner ℝ (-(Real.sin r * r') • N + (Real.cos r * r') • e + Real.sin r • f)
        (-(Real.sin r * r') • N + (Real.cos r * r') • e + Real.sin r • f)
      = (Real.sin r * r') ^ 2 + (Real.cos r * r') ^ 2 + (Real.sin r) ^ 2 * norm f ^ 2 := by
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    simp [hNe, hNf, hef, hN, he, real_inner_comm]
    ring
  rw [← real_inner_self_eq_norm_sq]
  rw [hinner]
  nlinarith [Real.sin_sq_add_cos_sq r]

end Commons.Analysis.InnerProductSpace
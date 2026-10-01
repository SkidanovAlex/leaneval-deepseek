import Mathlib
import Submission.Work.LinnikContract.Defs

namespace Work.A7

/-- Norm of HB's test function `F₂` restricted to the real axis: for real `λ`,
`F₂(K)(λ) = ((1 - e^{-Kλ})/λ)²` is a (nonnegative) real number, so its norm in `ℂ`
is that square. -/
theorem F2_norm_ofReal (K lam : ℝ) :
    ‖Work.LinnikContract.F2 K ((lam : ℂ))‖ = ((1 - Real.exp (-(K * lam))) / lam) ^ 2 := by
  have hF : Work.LinnikContract.F2 K ((lam : ℂ))
      = ((((1 - Real.exp (-(K * lam))) / lam : ℝ)) : ℂ) ^ 2 := by
    unfold Work.LinnikContract.F2
    have harg : (-(K : ℂ) * (lam : ℂ)) = ((-(K * lam) : ℝ) : ℂ) := by push_cast; ring
    rw [harg, ← Complex.ofReal_exp]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, ← Complex.ofReal_pow]
  rw [hF, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Work.A7
